/* MIT License

Copyright (c) 2022 Michael Rohs
Copyright (c) 2023 DosWorld

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE. */

#include <stdint.h>
#include "UTIL.H"
#include "RISC.H"
#include "SCAN.H"
#include "GEN.H"

#if 0
#define report_instruction(at) \
        printf("%3d (%-6s): ", at, __func__); R_print_instruction(G_code[at])
#else
#define report_instruction(at)
#endif

#define NAME(x) {x, #x}

struct {
    G_ClassMode klass;
    char* name;
} class_mode_names[] = {
    NAME(Head),
    NAME(Var), NAME(Par), NAME(Const), NAME(Fld), NAME(Typ), NAME(Proc), NAME(StdProc),
    NAME(Reg), NAME(Cond)
};
#define CLASS_MODE_COUNT (sizeof(class_mode_names) / sizeof(class_mode_names[0]))

struct {
    G_Form class;
    char* name;
} form_names[] = {
    NAME(Undefined), NAME(Boolean), NAME(Integer), NAME(Array), NAME(Record)
};
#define FORM_COUNT (sizeof(form_names) / sizeof(form_names[0]))

typedef enum { FP = 12, SP = 13, LNK = 14, PC = 15 } ReservedRegister;

/*
A (named) object in the source code. Example variants:
- G_Object variants (layout of objects if they are completely constructed):
- Var (local and global variables)
- Par (reference (VAR) parameters)
- Const (constant value)
- Fld (field of a record)
- Typ (declared type)
- Proc (procedure declaration)
- StdProc (standard procedure)
*/;

/*
Represents information about an object or an expression during code generation.
For example needed for delayed code generation.
*/;

G_Item G_make_item(void) {
    G_Item r;
    r.mode = Head;
    r.level = 0;
    r.type = G_undefined_type;
    r.a = 0;
    r.b = 0;
    r.c = 0;
    r.r = -1;
    return r;
}

G_Type* G_new_type(G_Form form, size_t size) {
    G_Type *t;
    // require("valid size", size >= 0);
    t = xcalloc(1, sizeof(G_Type));
    t->form = form;
    t->size = size;
    return t;
}

G_Type* G_undefined_type;
G_Type* G_bool_type;
G_Type* G_int_type;

size_t G_current_level;
INTEGER G_pc;
INTEGER G_entry;
static Set registers;
INTEGER G_code[G_MAX_CODE];


void G_print_item(G_Item* i) {
    char* form = "(null)";
    if(i->type != NULL) {
        form = form_names[i->type->form].name;
    }
    printf("G_Item(%s, %s, level=%d, a=%d, b=%d, c=%d, r=%d)\n",
           class_mode_names[i->mode].name,
           form,
           i->level, i->a, i->b, i->c, i->r);
}

void G_print_object(G_Object* o) {
    char* form = "(null)";
    if(o->type != NULL) {
        form = form_names[o->type->form].name;
    }
    printf("G_Object(%s, %s, %s, level=%d, value=%d)\n",
           o->name,
           class_mode_names[o->klass].name,
           form, o->level, o->value);
}

void G_print_type(G_Type* t) {
    char* base = "(null)";
    if(t->base != NULL) {
        base = form_names[t->base->form].name;
    }
    printf("G_Type(%s, base=%s, size=%d, len=%d)\n",
           form_names[t->form].name,
           base, t->size, t->len);
}

static void get_register(INTEGER* r) {
    require("register free", *r < 0 || *r >= FP);
    int i = 0;
    while(i < FP && in(i, registers)) {
        i++;
    }
    panic_if(i >= FP, "no free register found");
    incl(&registers, i);
    *r = i;
}

static void free_register(/*inout*/INTEGER* r) {
    INTEGER i = *r;
    if(i >= 0 && i < FP) {
        excl(&registers, i);
    }
    *r = -1;
}

static void put(INTEGER op, INTEGER a, INTEGER b, INTEGER c) {
    require("valid operation", op < BEQ);
    require("code array not full", G_pc < G_MAX_CODE);
    G_code[G_pc++] = R_encode_instruction(op, a, b, c);
    report_instruction(G_pc - 1);
}

static void put_BR(INTEGER op, INTEGER disp) {
    require("valid operation", op >= BEQ);
    require("code array not full", G_pc < G_MAX_CODE);
    G_code[G_pc++] = R_encode_instruction(op, 0, 0, disp);
    report_instruction(G_pc - 1);
}


static void test_range(INTEGER x) {
    if(x >= 0x20000 || x < -0x20000) {
        S_mark("value too large");
    }
}

static void load(G_Item* x) {
    require("not in Reg mode", x->mode != Reg);
    INTEGER r = -1;
    if(x->mode == Var) {
        if(x->r == PC) {
            x->a -= G_pc * 4;
        }
        get_register(&r);
        put(LDW, r, x->r, x->a);
        free_register(&x->r);
        x->r = r;
        x->mode = Reg;
    } else if(x->mode == Const) {
        test_range(x->a);
        get_register(&x->r);
        put(MOVI, x->r, 0, x->a);
        x->mode = Reg;
    } else {
        exit_if(true, "wrong mode %s", class_mode_names[x->mode].name);
    }
};

/*
Loads the boolean value denoted by x into a register. Also issues a CMPI(x,0)
instruction, so the comparison result will be in the N and Z flags. If x is
false (x = 0) then Z = 1. If x is true (x != 0) then Z = 0. So a subsequent BEQ
would branch if x is true.
*/;
static void load_bool(G_Item* x) {
    if(x->type->form != Boolean) {
        S_mark("Boolean?");
    }
    load(x);
    x->mode = Cond;
    x->a = 0;
    x->b = 0;
    x->c = 1;
    put(CMPI, 0, x->r, 0);
}

/*
Emits an operation of the form x := x OP y. The operations are:
MOV, MVN, ADD, SUB, MUL, Div, Mod, CMP.
*/;
static void put_op(INTEGER op, G_Item* x, G_Item* y) {
    require("valid range", MOV <= op && op <= CMP);
    if(x->mode != Reg) {
        load(x);
    }
    if(y->mode == Const ) {
        test_range(y->a);
        put(op + (MOVI - MOV), x->r, x->r, y->a);
    } else {
        if(y->mode != Reg) {
            load(y);
        }
        put(op, x->r, x->r, y->r);
        free_register(&y->r);
    }
}

/*
Negates the condition. Possible because of the arrangement of conditions in the
instructions: 0: =, 1: !=, 2: <, 3: >=, 4: <=, 5: >
*/;
static INTEGER negated(INTEGER cond) {
    return ODD(cond) ? cond - 1 : cond + 1;
}

/*
Concatenates two linked lists of incomplate forward jumps. Each branch
instruction refers to the preceding branch instruction in the list.
*/;
static INTEGER merged(INTEGER L0, INTEGER L1) {
    INTEGER L2, L3;
    if(L0 != 0) {
        L2 = L0;
        while(true ) {
            L3 = G_code[L2] & 0x03ffffff;
            if(L3 == 0 ) {
                break;
            }
            L2 = L3;
        }
        G_code[L2] = G_code[L2] - L3 + L1;
        report_instruction(L2);
        return L0;
    } else {
        return L1;
    }
}

void G_fix(INTEGER at, INTEGER with) {
    assert("branch instruction at destination", ((G_code[at] >> 26) & 0x3f) >= BEQ);
    G_code[at] = (G_code[at] & 0xfc000000) | (with & 0x03ffffff);
    report_instruction(at);
}

static void fix_with(INTEGER L0, INTEGER L1) {
    INTEGER L2;
    while(L0 != 0) {
        L2 = G_code[L0] & 0x03ffffff;
        G_fix(L0, L1 - L0);
        L0 = L2;
    }
}

void G_fix_link(INTEGER L) {
    INTEGER L_prev;
    while(L != 0) {
        L_prev = G_code[L] & 0x03ffffff;
        G_fix(L, G_pc - L);
        L = L_prev;
    }
}

void G_inc_level(size_t n) {
    require("valid offset", n == -1 || n == 1);
    G_current_level += n;
}

/*
Creates a constant value. It is not directly emmited as code, but stored in the
item. Most likely, it will later be used in an immediate-mode instruction.
*/;
void G_make_const_item(/*out*/G_Item* x, G_Type* type, INTEGER value) {
    require("register not in use", x->r == -1 || x->r >= FP);
    x->mode = Const;
    x->type = type;
    x->a = value;
}

/*
Sets the attributes of item x according to object y. Copies class (to mode),
type, level, and value (to a). Sets r to the appropriate base register index.
Called from: factor and statement_sequence. From statement_sequence either
called as the left-hand side of an assignment or as a procedure name in a
procedure call.

Var (local and global variables)
Par (reference (VAR) parameters)
Const (constant value)
Fld (field of a record)
Typ (declared type)
Proc (procedure declaration)
StdProc (standard procedure)
*/;
void G_item_from_object(/*out*/G_Item* x, /*in*/G_Object* y) {
    INTEGER r = -1;
    x->mode = y->klass;
    x->type = y->type;
    x->level = y->level;
    x->a = y->value;
    x->b = 0;
    if(y->level == 0) {
        x->r = PC;
    } else if(y->level == G_current_level) {
        x->r = FP;
    } else {
        S_mark("access to intermediary levels (surrounding procedures) is not allowed");
        x->r = -1;
    }
    if(y->klass == Par) {
        get_register(&r);
        put(LDW, r, x->r, x->a);
        x->mode = Var;
        x->r = r;
        x->a = 0;
    }

};

void G_field(/*inout*/G_Item* x, /*in*/G_Object* y) {
    require("x is a record", x->type->form == Record);
    x->a += y->value;
    x->type = y->type;
};


void G_index(/*inout*/G_Item* x, /*in*/G_Item* y) {
    require("x is an array", x->type->form == Array);
    require("valid mode", x->mode == Var || x->mode == Const);
    if(y->type != G_int_type) {
        S_mark("index not integer");
    }
    if(y->mode == Const) {
        if(y->a < 0 || y->a >= x->type->len ) {
            S_mark("bad index");
        }
        x->a += y->a * x->type->base->size;
    } else {
        if(y->mode != Reg) {
            load(y);
        }
        put(CHKI, y->r, 0, x->type->len);
        put(MULI, y->r, y->r, x->type->base->size);
        if(x->r == PC ) {
            put(ADD, y->r, x->r, y->r);
            put(SUBI, y->r, y->r, 4 * G_pc - 4);
        } else {
            put(ADD, y->r, x->r, y->r);
        }
        free_register(&x->r);
        x->r = y->r;
    }
    x->type = x->type->base;
};

/*
factor = integer | "(" expression ")" | "~" factor.
term = factor {"&" factor}.
SimpleExpression = term {"OR" term}.
expression = SimpleExpression [("=" | "#" | "<" | "<=" | ">" | ">=") SimpleExpression].
*/;


void G_op1(S_Symbol op, /*inout*/G_Item* x) {
    INTEGER t;
    if(op == s_minus) {
        if(x->type->form != Integer) {
            S_mark("bad type");
        } else if(x->mode == Const) {

            x->a = -x->a;
        } else {
            if(x->mode != Reg) {
                load(x);
            }
            put(MVN, x->r, 0, x->r);
        }
    } else if(op == s_not) {
        if(x->mode != Cond) {
            load_bool(x);
        }
        x->c = negated(x->c);

        t = x->a;
        x->a = x->b;
        x->b = t;
        free_register(&x->r);
    } else if(op == s_and) {
        if(x->mode != Cond) {
            load_bool(x);
        }
        put_BR(BEQ + negated(x->c), x->a);
        free_register(&x->r);
        x->a = G_pc - 1;
        G_fix_link(x->b);
        x->b = 0;
    } else if(op == s_or) {
        if(x->mode != Cond) {
            load_bool(x);
        }
        put_BR(BEQ + x->c, x->b);
        free_register(&x->r);
        x->b = G_pc - 1;
        G_fix_link(x->a);

        x->a = 0;
    }
};


void G_op2(S_Symbol op, /*inout*/G_Item* x, /*in*/G_Item* y) {
    if(x->type->form == Integer && y->type->form == Integer) {
        if(x->mode == Const && y->mode == Const) {
            if(op == s_plus) {
                x->a += y->a;
            } else if(op == s_minus) {
                x->a -= y->a;
            } else if(op == s_times) {
                x->a = x->a * y->a;
            } else if(op == s_div) {
                x->a = x->a / y->a;
            } else if(op == s_mod) {
                x->a = R_mod(x->a, y->a);
            } else {
                S_mark("bad type");
            }
        } else {
            if(op == s_plus) {
                put_op(ADD, x, y);
            } else if(op == s_minus) {
                put_op(SUB, x, y);
            } else if(op == s_times) {
                put_op(MUL, x, y);
            } else if(op == s_div) {
                put_op(Div, x, y);
            } else if(op == s_mod) {
                put_op(Mod, x, y);
            } else {
                S_mark("bad type");
            }
        }
    } else if(x->type->form == Boolean && y->type->form == Boolean) {
        if(y->mode != Cond) {
            load_bool(y);
        }
        if(op == s_or) {
            x->a = y->a;
            x->b = merged(y->b, x->b);
            x->c = y->c;
        } else if(op == s_and) {
            x->a = merged(y->a, x->a);
            x->b = y->b;
            x->c = y->c;
        } else {
            S_mark("bad type");
        }
    } else {
        S_mark("bad type");
    }
    free_register(&y->r);
};

/*
Emits code to check the given relation. The relations are: s_eql = 9, s_neq =
10, s_lss = 11, s_geq = 12, s_leq = 13, s_gtr = 14 (see scanner symbols)
*/;
void G_relation(S_Symbol op, /*inout*/G_Item* x, /*in*/G_Item* y) {
    require("valid relation", s_eql <= op && op <= s_gtr);
    if(x->type->form != Integer || y->type->form != Integer) {
        S_mark("bad type");
    } else {
        put_op(CMP, x, y);
        x->c = op - s_eql;
    }
    x->mode = Cond;
    x->type = G_bool_type;
    x->a = 0;
    x->b = 0;
};

/*
Checks if type1 is a legal actual parameter type for the formal parameter type
type2.
*/;
static bool parameter_compatible(G_Type* actual_type, G_Type* formal_type) {
    if(actual_type == G_undefined_type || formal_type == G_undefined_type) {
        return false;
    }
    if(actual_type->form != formal_type->form) {
        return false;
    }
    if(actual_type->form == Integer) {
        return true;
    }
    if(actual_type->form == Boolean) {
        return true;
    }
    if(actual_type->form == Array) {
        return actual_type->len == formal_type->len && \
               parameter_compatible(actual_type->base, formal_type->base);
    }
    if(actual_type->form == Record) {
        return actual_type == formal_type;
    }
    return false;
}


static bool assignment_compatible(G_Type* destination, G_Type* source) {
    return parameter_compatible(destination, source);
}

static void store_array(G_Item* x, G_Item* y) {
    int size = x->type->size;
    INTEGER cap = -1, src = -1, dst = -1, r = -1;
    require("destination is array", x->type->form == Array);
    require("source is array", y->type->form == Array);
    require("valid mode", x->mode == Var);
    require("valid mode", y->mode == Var);
    get_register(&cap);
    get_register(&src);
    get_register(&dst);
    get_register(&r);
    put(ADDI, src, y->r, y->a - G_pc * 4 * (y->r == PC));
    put(ADDI, dst, x->r, x->a - 4 - G_pc * 4 * (x->r == PC));
    put(ADDI, cap, src, size);
    put(CMP, 0, src, cap);
    put_BR(BGE, 4);
    put(POP, r, src, 4);
    put(PSH, r, dst, -4);
    put_BR(BR, -4);
    free_register(&cap);
    free_register(&src);
    free_register(&dst);
    free_register(&r);
};

static void store_record(G_Item* x, G_Item* y) {
    int size = x->type->size;
    INTEGER cap = -1, src = -1, dst = -1, r = -1;
    require("destination is record", x->type->form == Record);
    require("source is record", y->type->form == Record);
    get_register(&cap);
    get_register(&src);
    get_register(&dst);
    get_register(&r);
    put(ADDI, src, y->r, y->a - G_pc * 4 * (y->r == PC));
    put(ADDI, dst, x->r, x->a - 4 - G_pc * 4 * (x->r == PC));
    put(ADDI, cap, src, size);
    put(CMP, 0, src, cap);
    put_BR(BGE, 4);
    put(POP, r, src, 4);
    put(PSH, r, dst, -4);
    put_BR(BR, -4);
    free_register(&cap);
    free_register(&src);
    free_register(&dst);
    free_register(&r);
};


void G_store(/*inout*/G_Item* x, /*in*/G_Item* y) {
    if(assignment_compatible(x->type, y->type)) {
        G_Form x_form = x->type->form;
        if(x_form == Integer || x_form == Boolean) {
            if(y->mode == Cond ) {
                put_BR(BEQ + negated(y->c), y->a);
                free_register(&y->r);
                y->a = G_pc - 1;
                G_fix_link(y->b);
                get_register(&y->r);
                put(MOVI, y->r, 0, 1);
                put_BR(BR, 2);
                G_fix_link(y->a);
                put(MOVI, y->r, 0, 0);
            } else if(y->mode != Reg) {
                load(y);
            }
            if(x->mode == Var) {
                put(STW, y->r, x->r, x->a - G_pc * 4 * (x->r == PC));
            } else {
                S_mark("illegal assignment");
            }
            free_register(&x->r);
            free_register(&y->r);
        } else if(x_form == Array) {
            store_array(x, y);
            free_register(&x->r);
            free_register(&y->r);
        } else if(x_form == Record) {
            store_record(x, y);
            free_register(&x->r);
            free_register(&y->r);
        } else {
            S_mark("incompatible assignment");
        }
    } else {
        S_mark("incompatible assignment");
    }
}

/*
Checks if x is a parameter that corresponds to the given type and class and, if
so, generates code to push the parameter onto the stack.
*/;
void G_parameter(G_Item* x, G_Type* fp_type, G_ClassMode fp_class) {
    INTEGER a, r;
    if(parameter_compatible(x->type, fp_type)) {
        if(fp_class == Par) {
            if(x->mode == Var) {
                a = x->a;
                if(x->r == PC) {
                    a -= 4 * G_pc;
                }
                if(a != 0 ) {
                    r = -1;
                    get_register(&r);
                    put(ADDI, r, x->r, a);
                    free_register(&x->r);
                    x->r = r;
                }
            } else {
                S_mark("illegal parameter mode");
            }
        } else if(fp_class == Var ) {

            if(x->mode != Reg ) {
                load(x);
            }
        } else {
            exit_if(true, "invalid parameter class %d", fp_class);
        }
        put(PSH, x->r, SP, 4);
        free_register(&x->r);
    } else {
        S_mark("bad parameter type");
    }
}

/*
Emits a conditional forward jump with unknown destination address. Will be fixed
once it is known.
*/;
void G_cond_forward_jump(G_Item* x) {
    if(x->type->form == Boolean) {
        if(x->mode != Cond ) {
            load_bool(x);
        }
        put_BR(BEQ + negated(x->c), x->a);
        free_register(&x->r);
        G_fix_link(x->b);
        x->a = G_pc - 1;
    } else {
        S_mark("Boolean?");
        x->a = G_pc;
    }
}

void G_backward_jump(INTEGER L) {
    put_BR(BR, L - G_pc);
}

void G_forward_jump(INTEGER* L) {
    put_BR(BR, *L);
    *L = G_pc - 1;
}

void G_call(G_Item* x) {
    put_BR(BSR, x->a - G_pc);
}

void G_io_read(G_Item* y) {
    G_Item z = G_make_item();
    get_register(&z.r);
    z.mode = Reg;
    z.type = G_int_type;
    put(RD, z.r, 0, 0);
    G_store(y, &z);
}

void G_io_write(G_Item* y) {
    if (y->mode != Reg) {
        load(y);
    }
    put(WRD, 0, 0, y->r);
    free_register(&y->r);
}

void G_io_write_hex(G_Item* y) {
    if(y->mode != Reg) {
        load(y);
    }
    put(WRH, 0, 0, y->r);
    free_register(&y->r);
}

void G_io_read_byte(G_Item* y) {
    G_Item z = G_make_item();
    get_register(&z.r);
    z.mode = Reg;
    z.type = G_int_type;
    put(RB, z.r, 0, 0);
    G_store(y, &z);
}

void G_io_write_byte(G_Item* y) {
    if(y->mode != Reg) {
        load(y);
    }
    put(WRB, 0, 0, y->r);
    free_register(&y->r);
}

void G_io_write_line(void) {
    put(WRL, 0, 0, 0);
}

void G_inc_dec(bool inc, G_Item* y, G_Item* delta) {
    int pc_relative;
    INTEGER r;
    if(y->mode == Var) {
        pc_relative = 4 * (y->r == PC);
        r = -1;
        get_register(&r);
        put(LDW, r, y->r, y->a - pc_relative * G_pc);
        if(delta->mode == Const) {
            put(inc ? ADDI : SUBI, r, r, delta->a);
        } else {
            if(delta->mode != Reg) {
                load(delta);
            }
            put(inc ? ADD : SUB, r, r, delta->r);
            free_register(&delta->r);
        }
        put(STW, r, y->r, y->a - pc_relative * G_pc);
        free_register(&r);
        free_register(&y->r);
    } else {
        S_mark("illegal assignment");
    }
};

static void put_string(const char* s) {
    INTEGER r = -1;
    get_register(&r);
    while(*s) {
        put(MOVI, r, 0, *s);
        put(WRB, 0, 0, r);
        s++;
    }
    free_register(&r);
}

static void put_number(int i) {
    INTEGER r = -1;
    get_register(&r);
    put(MOVI, r, 0, i);
    put(WRD, 0, 0, r);
    free_register(&r);
}

void G_assert(G_Item* y) {
    size_t line, column;
    INTEGER branch_location;
    if(y->type->form == Boolean) {
        if(y->mode != Cond) {
            load_bool(y);
        }
        branch_location = G_pc;
        put_BR(BEQ + y->c, 0);
        free_register(&y->r);
        G_fix_link(y->b);
        line = 0;
        column = 0;
        S_line_and_column(&line, &column);
        if(column == 0) {
            line--;
        }
        put_string("ASSERT failed, line:");
        put_number(line);
        put(WRL, 0, 0, 0);
        put(MOVI, LNK, 0, 0);
        put_BR(RET, LNK);
        G_fix_link(branch_location);
    } else {
        S_mark("Boolean?");
    }
}

/*
Sets module entry point and emit code to initialize stack pointer and push
initial link register value (0).
Memory layout:
- [above_code to R_MEM_SIZE): runtime stack
- [R_PROG_ORG to end_of_code): code
- [R_PROG_ORG - varsize, R_PROG_ORG): global variables of the module
*/;
void G_header(void) {
    G_entry = G_pc;
    put(MOVI, SP, 0, R_MEM_SIZE);
    put(PSH, LNK, SP, 4);
}

void G_enter(INTEGER size) {
    put(PSH, LNK, SP, 4);
    put(PSH, FP, SP, 4);
    put(MOV, FP, 0, SP);
    put(SUBI, SP, SP, size);
}

void G_return(INTEGER size) {
    put(MOV, SP, 0, FP);
    put(POP, FP, SP, 4);
    put(POP, LNK, SP, size + 4);
    put_BR(RET, LNK);
}

void G_open(void) {
    G_current_level = 0;
    G_pc = 0;
    G_entry = 0;
    registers = make_set();
}

void G_close(INTEGER globals) {
    put(POP, LNK, SP, 4);
    put_BR(RET, LNK);
    ensure("all registers free", registers.s == 0);
}

void G_init(void) {
    G_undefined_type = G_new_type(Undefined, R_WORD_SIZE);
    G_undefined_type->base = G_undefined_type;
    G_bool_type = G_new_type(Boolean, R_WORD_SIZE);
    G_int_type = G_new_type(Integer, R_WORD_SIZE);
}

