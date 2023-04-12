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

/*
Oberon-0 EBNF Grammar

ident = letter {letter | digit}.
integer = digit {digit}.

selector = {"." ident | "[" expression "]"}.

factor = ident selector | integer | "(" expression ")" | "~" factor.
term = factor {("*" | "DIV" | "MOD" | "&") factor}.
SimpleExpression = ["+"|"-"] term {("+"|"-" | "OR") term}.
expression = SimpleExpression [("=" | "#" | "<" | "<=" | ">" | ">=") SimpleExpression].

assignment = ident selector ":=" expression.

ActualParameters = "(" [expression {"," expression}] ")" .
ProcedureCall = ident [ActualParameters].

IfStatement = "IF" expression "THEN" StatementSequence
              {"ELSIF" expression "THEN" StatementSequence}
              ["ELSE" StatementSequence] "END".

WhileStatement = "WHILE" expression "DO" StatementSequence "END".

statement = [assignment | ProcedureCall | IfStatement | WhileStatement].
StatementSequence = statement {";" statement}.

IdentList = ident {"," ident}.
ArrayType = "ARRAY" expression "OF" type.
FieldList = [IdentList ":" type].
RecordType = "RECORD" FieldList {";" FieldList} "END".
type = ident | ArrayType | RecordType.

FPSection = ["VAR"] IdentList ":" type.
FormalParameters = "(" [FPSection {";" FPSection}] ")".

ProcedureHeading = "PROCEDURE" ident [FormalParameters].
ProcedureBody = declarations ["BEGIN" StatementSequence] "END".
ProcedureDeclaration = ProcedureHeading ";" ProcedureBody ident.

declarations = ["CONST" {ident "=" expression ";"}]
    ["TYPE" {ident "=" type ";"}]
    ["VAR" {IdentList ":" type ";"}]
    {ProcedureDeclaration ";"}.

module = "MODULE" ident ";" declarations ["BEGIN" StatementSequence] "END" ident "." .
*/;

static S_Symbol sym = s_null;

/*
Linked lists of objects. All lists end with the guard object. Each scope starts
with a header object that links to the first object of this scope (next pointer)
and the header of the next scope below it (dsc pointer).
*/;


static G_Object* top_scope = NULL;
static G_Object* universe = NULL;
static G_Object* guard = NULL;
static G_Object* forward_calls = NULL;

/*
Creates a new object of the given class and adds it to the topmost scope.
Assumes that the scanner has just read the identifier of the object. Only
creates the object if it does not already appear in the top scope. Only sets the
"name", "class", and "next" attributes of the new object.

An object can be the name of a variable, a value parameter, a variable
parameter, a constant, a field, a type, or a procedure. See G_ClassMode in
generator.
*/;
static void new_object(/*out*/G_Object** obj, G_ClassMode klass) {
    G_Object* new;
    G_Object* x = top_scope;

    strcpy(guard->name, S_identifier);
    while(strcmp(x->next->name, S_identifier) != 0 ) {
        x = x->next;
    }
    if(x->next == guard ) {
        new = xcalloc(1, sizeof(G_Object));
        strcpy(new->name, S_identifier);
        new->klass = klass;
        new->type = G_undefined_type;
        new->next = guard;
        x->next = new;
        *obj = new;
    } else {
        *obj = x->next;
        S_mark("duplicate definition");
    }
    ensure_not_null(*obj);
}

/*
G_Object variants:
Var (local and global variables)
Par (reference (VAR) parameters)
Const (constant value)
Fld (field of a record)
Typ (declared type)
Proc (procedure declaration)
StdProc (standard procedure)


Var (local and global variables):
name  = <identifier>
class = Var
type  = parsed type
value = negative offset relative to base, base is FP (local) or PC (global),
        for int variables, first variable has value -4, second variable
        has value -8, etc.)
level = current level (0 for global variables, 1 for local variables in global
        procedures, etc.)


Var (value parameters):
name  = <identifier>
class = Var
type  = parsed type
value = positive offset relative to base, base is FP, G_MARK_SIZE (for return
        address and old FP) is 2 words (8 bytes)
        for 2 int parameters, first parameter has value 12, second parameter
        has value 8); for value parameters, the value of the actual parameter
        is located on the stack
level = current level (0 for global variables, 1 for local variables in global
        procedures, etc.)


Par (reference (VAR) parameters):
name  = <identifier>
class = Par
type  = stated type
value = positive offset relative to base, base is FP, G_MARK_SIZE (for return
        address and old FP) is 2 words (8 bytes)
        for 2 int parameters, first parameter has value 12, second parameter
        has value 8); for variable parameters, the address of the actual parameter
        is located on the stack
level = current level (1 for local variables in global procedures, etc.)


Const (constant value):
name  = <identifier>
class = Const
type  = type of constant value
value = constant value
level = current level (0 for global constants, 1 for local constantsin global
        procedures, etc.)


Fld (field of a record):
name  = <identifier>
class = Fld
type  = parsed type
value = non-negative offset relative to start of record,
        for 2 int fields, first field has value 0 and second field has value 4
level = 0


Typ (declared type):
name  = <identifier>
class = Typ
type  = parsed type
value = 0
level = 0


Proc (procedure declaration):
name  = <identifier>
class = Proc
type  = NULL
value = -1 of declared, but not defined; index of first instruction of procedure
        in code array, i.e. start of prologue
level = 0
dsc = formal parameter list


StdProc (standard procedure):
name  = <identifier>
class = StdProc
type  = NULL
value = <value used as argument to enter function>
level = 0
*/;

/*
Tries to find an object in any scope. Assumes that the scanner has just read the
identifier of the object. Returns the guard object if no object with the given
identifier exists.
*/;
static void find(/*out*/G_Object** obj) {
    G_Object* s = top_scope;
    strcpy(guard->name, S_identifier);
    while(true) {
        G_Object* x = s->next;
        while(strcmp(x->name, S_identifier) != 0) {
            x = x->next;
        }
        if(x != guard) {
            *obj = x;
            break;
        }
        if(s == universe) {
            *obj = x;
            S_mark("undef");
            break;
        }
        s = s->dsc;
    }
    ensure_not_null(*obj);
}

/*
Tries to find an object in the list. Assumes that the scanner has just read the
identifier of the object. Returns the guard object if no object with the given
identifier exists.
*/;
static void find_field(/*out*/G_Object** obj, G_Object* list) {
    strcpy(guard->name, S_identifier);
    while(strcmp(list->name, S_identifier) != 0) {
        list = list->next;
    }
    *obj = list;
    ensure_not_null(*obj);
}

/*
Checks if obj is a procedure parameter. Local variables have address offset
value < 0 (relative to FP). Global variables also have address offset < 0
(relative to PC). Value parameters have value > 0.
*/;
static BOOLEAN is_param(G_Object* obj) {
    return obj->klass == Par || (obj->klass == Var && obj->value > 0);
}

static void open_scope(void) {
    G_Object* s = xcalloc(1, sizeof(G_Object));
    s->klass = Head;
    s->dsc = top_scope;
    s->next = guard;
    top_scope = s;
}

static void close_scope(void) {
    top_scope = top_scope->dsc;
}

static void expression(G_Item* x);

static void selector(/*inout*/G_Item* x) {
    G_Object* obj;
    G_Item y = G_make_item();

    while(sym == s_lbrak || sym == s_period) {
        if(sym == s_lbrak) {
            S_get(&sym);
            expression(&y);
            if(x->type->form == Array) {
                G_index(x, &y);
            } else {
                S_mark("not an array");
            }
            if(sym == s_rbrak) {
                S_get(&sym);
            } else {
                S_mark("]?");
            }
        } else {
            S_get(&sym);
            if(sym == s_ident) {
                if(x->type->form == Record) {
                    find_field(&obj, x->type->fields);
                    S_get(&sym);
                    if(obj != guard) {
                        G_field(x, obj);
                    } else {
                        S_mark("undef");
                    }
                } else {
                    S_mark("not a record");
                }
            } else {
                S_mark("ident?");
            }
        }
    }
}

static void factor(/*out*/G_Item* x) {
    G_Object* obj;

    if(sym < s_lparen) {
        S_mark("ident?");
        do {
            S_get(&sym);
        } while (sym < s_lparen);
    }
    if(sym == s_ident) {
        find(&obj);
        S_get(&sym);
        G_item_from_object(x, obj);
        selector(x);
    } else if(sym == s_number) {
        G_make_const_item(x, G_int_type, S_value);
        S_get(&sym);
    } else if(sym == s_lparen) {
        S_get(&sym);
        expression(x);
        if(sym == s_rparen) {
            S_get(&sym);
        } else {
            S_mark(")?");
        }
    } else if(sym == s_not) {
        S_get(&sym);
        factor(x);
        G_op1(s_not, x);
    } else {
        S_mark("factor?");
        G_item_from_object(x, guard);
    }
}

static void term(/*out*/G_Item* x) {
    G_Item y = G_make_item();
    S_Symbol op;

    factor(x);
    while(sym >= s_times && sym <= s_and) {
        op = sym;
        S_get(&sym);
        if(op == s_and ) {
            G_op1(op, x);
        }
        factor(&y);
        G_op2(op, x, &y);
    }
}

static void simple_expression(/*out*/G_Item* x) {
    G_Item y = G_make_item();
    S_Symbol op;

    if(sym == s_plus) {
        S_get(&sym);
        term(x);
    } else if(sym == s_minus) {
        S_get(&sym);
        term(x);
        G_op1(s_minus, x);
    } else {
        term(x);
    }
    while(sym >= s_plus && sym <= s_or) {
        op = sym;
        S_get(&sym);
        if(op == s_or ) {
            G_op1(op, x);
        }
        term(&y);
        G_op2(op, x, &y);
    }
}

static void expression(/*out*/G_Item* x) {
    G_Item y = G_make_item();
    S_Symbol op;

    simple_expression(x);
    if(sym >= s_eql && sym <= s_gtr) {
        op = sym;
        S_get(&sym);
        simple_expression(&y);
        G_relation(op, x, &y);
    }
}

/*
Parses a single parameter in an actual parameter list and checks whether it is
compatible with the given formal parameter. Then sets the argument to the next
parameter (if any).
ActualParameters = "(" [expression {"," expression}] ")" .
*/;
static void parameter(/*out*/G_Object** p_formal_parameter) {
    G_Object* formal_parameter = *p_formal_parameter;
    G_Item x = G_make_item();

    expression(&x);
    if(is_param(formal_parameter)) {
        G_parameter(&x, formal_parameter->type, formal_parameter->klass);
        formal_parameter = formal_parameter->next;
    } else {
        S_mark("too many parameters");
    }
    *p_formal_parameter = formal_parameter;
}

static void std_proc_call_param(/*out*/G_Item* x) {
    if(sym == s_lparen) {
        S_get(&sym);
    } else {
        S_mark("(?");
    }
    expression(x);
    if(sym == s_rparen) {
        S_get(&sym);
    } else {
        S_mark(")?");
    }
}

static void std_proc_call(/*in*/G_Item* x, /*out*/G_Item* y) {
    G_Item delta;
    int std_proc_number;

    require("x is standard procedure", x->mode == StdProc);
    delta = G_make_item();
    std_proc_number = x->a;
    switch(std_proc_number) {
    case 1: {
        std_proc_call_param(y);
        if(y->type->form != Integer) {
            S_mark("not integer");
        }
        G_io_read(y);
        break;
    }
    case 2: {
        std_proc_call_param(y);
        if(y->type->form != Integer && y->type->form != Boolean) {
            S_mark("neither integer nor boolean");
        }
        G_io_write(y);
        break;
    }
    case 3: {
        std_proc_call_param(y);
        if(y->type->form != Integer) {
            S_mark("not integer");
        }
        G_io_write_hex(y);
        break;
    }
    case 4: {
        std_proc_call_param(y);
        if(y->type->form != Integer) {
            S_mark("not integer");
        }
        G_io_read_byte(y);
        break;
    }
    case 5: {
        std_proc_call_param(y);
        if(y->type->form != Integer) {
            S_mark("not integer");
        }
        G_io_write_byte(y);
        break;
    }
    case 6: {
        if(sym == s_lparen) {
            S_get(&sym);
            if(sym == s_rparen) {
                S_get(&sym);
            } else {
                S_mark(")?");
            }
        }
        G_io_write_line();
        break;
    }
    case 7:
    case 8: {
        if(sym == s_lparen) {
            S_get(&sym);
        } else {
            S_mark("(?");
        }
        expression(y);
        if(y->type->form != Integer) {
            S_mark("not integer");
        }
        if(sym == s_comma) {
            S_get(&sym);
            expression(&delta);
        } else {
            G_make_const_item(&delta, G_int_type, 1);
        }
        if(delta.type->form != Integer) {
            S_mark("not integer");
        }
        if(sym == s_rparen) {
            S_get(&sym);
        } else {
            S_mark(")?");
        }
        G_inc_dec(std_proc_number == 7, y, &delta);
        break;
    }
    case 9: {
        std_proc_call_param(y);
        if(y->type->form != Boolean) {
            S_mark("not boolean");
        }
        G_assert(y);
        break;
    }
    default:
        exit_if(true, "invalid standard procedure number %d", std_proc_number);
    }
}

static void add_forward_call(G_Object* proc, int pc) {
    G_Object* obj = xcalloc(1, sizeof(G_Object));
    obj->value = pc;
    obj->dsc = proc;
    obj->next = forward_calls;
    forward_calls = obj;
}

static void fix_foward_calls(void) {
    int at, with;
    G_Object* obj = forward_calls;

    while(obj != NULL) {
        at = obj->value;
        with = obj->dsc->value - at;
        G_fix(at, with);
        obj = obj->next;
    }
}

static void statement_sequence(void) {
    G_Object *formal_parameters;
    G_Object *obj;
    G_Item x = G_make_item();
    G_Item y = G_make_item();
    INTEGER L;

    while(true) {
        obj = guard;
        if(sym < s_ident) {
            S_mark("statement?");
            do {
                S_get(&sym);
            } while (sym < s_ident);
        }
        if(sym == s_ident) {
            find(&obj);
            S_get(&sym);
            G_item_from_object(&x, obj);
            selector(&x);
            if(sym == s_becomes) {
                S_get(&sym);
                expression(&y);
                G_store(&x, &y);
            } else if(sym == s_eql) {
                S_mark(":= ?");
                S_get(&sym);
                expression(&y);
                G_store(&x, &y);
            } else if(x.mode == Proc) {
                formal_parameters = obj->dsc;
                if(sym == s_lparen) {
                    S_get(&sym);
                    if(sym == s_rparen) {
                        S_get(&sym);
                    } else {
                        while(true) {
                            parameter(&formal_parameters);
                            if(sym == s_comma) {
                                S_get(&sym);
                            } else if(sym == s_rparen) {
                                S_get(&sym);
                                break;
                            } else if(sym >= s_semicolon) {
                                break;
                            } else {
                                S_mark(") or , ?");
                            }
                        }
                    }
                }
                if(!is_param(formal_parameters) ) {
                    if(obj->value < 0) {
                        add_forward_call(obj, G_pc);
                    }
                    G_call(&x);
                } else {
                    S_mark("too few parameters");
                }
            } else if(x.mode == StdProc) {
                std_proc_call(&x, &y);
            } else if(obj->klass == Typ) {
                S_mark("illegal assignment?");
            } else {
                S_mark("statement?");
            }
        } else if(sym == s_if) {
            S_get(&sym);
            expression(&x);
            G_cond_forward_jump(&x);
            if(sym == s_then) {
                S_get(&sym);
            } else {
                S_mark("THEN?");
            }
            statement_sequence();
            L = 0;
            while(sym == s_elsif) {
                S_get(&sym);
                G_forward_jump(&L);
                G_fix_link(x.a);
                expression(&x);
                G_cond_forward_jump(&x);
                if(sym == s_then ) {
                    S_get(&sym);
                } else {
                    S_mark("THEN?");
                }
                statement_sequence();
            }
            if(sym == s_else) {
                S_get(&sym);
                G_forward_jump(&L);
                G_fix_link(x.a);
                statement_sequence();
            } else {
                G_fix_link(x.a);
            }
            G_fix_link(L);
            if(sym == s_end) {
                S_get(&sym);
            } else {
                S_mark("END?");
            }
        } else if(sym == s_while) {
            S_get(&sym);
            L = G_pc;
            expression(&x);
            G_cond_forward_jump(&x);
            if(sym == s_do) {
                S_get(&sym);
            } else {
                S_mark("DO?");
            }
            statement_sequence();
            G_backward_jump(L);
            G_fix_link(x.a);
            if(sym == s_end) {
                S_get(&sym);
            } else {
                S_mark("END?");
            }
        }
        if(sym == s_semicolon) {
            S_get(&sym);
        } else if((sym >= s_semicolon && sym < s_if) || sym >= s_array) {
            break;
        } else {
            S_mark("; ?");
        }
    }
}

/*
Parses a comma-separated list of identifiers. Creates an object for each one and
returns a pointer to the first created object.
IdentList = ident {"," ident}.
*/;
static void identifier_list(G_ClassMode klass, /*out*/G_Object** first) {
    G_Object* obj;

    if(sym == s_ident) {
        new_object(first, klass);
        S_get(&sym);
        while(sym == s_comma) {
            S_get(&sym);
            if(sym == s_ident) {
                new_object(&obj, klass);
                S_get(&sym);
            } else {
                S_mark("ident?");
            }
        }
        if(sym == s_colon) {
            S_get(&sym);
        } else {
            S_mark(":?");
        }
    }
}

static void P_type(/*out*/G_Type** type) {
    G_Object* obj;
    G_Object* first;
    G_Item x = G_make_item();
    G_Type* tp;
    size_t size;
    *type = G_int_type;

    if(sym != s_ident && sym < s_array) {
        S_mark("type?");
        do {
            S_get(&sym);
        } while (sym != s_ident && sym < s_array);
    }
    if(sym == s_ident) {
        find(&obj);
        S_get(&sym);
        if(obj->klass == Typ) {
            *type = obj->type;
        } else {
            S_mark("type?");
        }
    } else if(sym == s_array) {
        S_get(&sym);
        expression(&x);
        if(x.mode != Const || x.a < 0) {
            S_mark("bad index");
        }
        if(sym == s_of) {
            S_get(&sym);
        } else {
            S_mark("OF?");
        }
        P_type(&tp);
        *type = G_new_type(Array, x.a * tp->size);
        (*type)->base = tp;
        (*type)->len = x.a;
    } else if(sym == s_record) {
        S_get(&sym);
        size = 0;
        open_scope();
        while(true) {
            if(sym == s_ident) {
                identifier_list(Fld, &first);
                P_type(&tp);
                obj = first;
                while(obj != guard) {
                    obj->type = tp;
                    obj->value = size;
                    size += obj->type->size;
                    obj = obj->next;
                }
            }
            if(sym == s_semicolon) {
                S_get(&sym);
            } else if(sym == s_ident) {
                S_mark("; ?");
            } else {
                break;
            }
        }
        *type = G_new_type(Record, size);
        (*type)->fields = top_scope->next;
        close_scope();
        if(sym == s_end) {
            S_get(&sym);
        } else {
            S_mark("END?");
        }
    } else {
        S_mark("ident?");
    }
}

static void declarations(INTEGER* varsize) {
    G_Object* obj;
    G_Object* first;
    G_Item x;
    G_Type* tp;

    if(sym < s_const && sym != s_end) {
        S_mark("declaration?");
        do {
            S_get(&sym);
        } while (sym < s_const && sym != s_end);
    }
    while(true) {
        if(sym == s_const) {
            S_get(&sym);
            while(sym == s_ident) {
                new_object(&obj, Const);
                S_get(&sym);
                if(sym == s_eql) {
                    S_get(&sym);
                } else {
                    S_mark("=?");
                }
                x = G_make_item();
                expression(&x);
                if(x.mode == Const) {
                    obj->value = x.a;
                    obj->type = x.type;
                } else {
                    S_mark("expression not constant");
                }
                if(sym == s_semicolon) {
                    S_get(&sym);
                } else {
                    S_mark(";?");
                }
            }
        }
        if(sym == s_type) {
            S_get(&sym);
            while(sym == s_ident) {
                new_object(&obj, Typ);
                S_get(&sym);
                if(sym == s_eql) {
                    S_get(&sym);
                } else {
                    S_mark("=?");
                }
                P_type(&obj->type);
                if(sym == s_semicolon) {
                    S_get(&sym);
                } else {
                    S_mark(";?");
                }
            }
        }
        if(sym == s_var) {
            S_get(&sym);
            while(sym == s_ident) {
                identifier_list(Var, &first);
                P_type(&tp);
                obj = first;
                while(obj != guard) {
                    obj->type = tp;
                    obj->level = G_current_level;
                    *varsize += obj->type->size;
                    obj->value = -*varsize;
                    obj = obj->next;
                }
                if(sym == s_semicolon ) {
                    S_get(&sym);
                } else {
                    S_mark("; ?");
                }
            }
        }
        if(sym >= s_const && sym <= s_var ) {
            S_mark("declaration?");
        } else {
            break;
        }
    }
}

static void procedure_decl_fp_section(INTEGER* parblksize) {
    G_Object* obj;
    G_Object* first;
    G_Type* tp;
    INTEGER parsize;

    if(sym == s_var) {
        S_get(&sym);
        identifier_list(Par, &first);
    } else {
        identifier_list(Var, &first);
    }
    if(sym == s_ident) {
        find(&obj);
        S_get(&sym);
        if(obj->klass == Typ ) {
            tp = obj->type;
        } else {
            S_mark("ident?");
            tp = G_int_type;
        }
    } else {
        S_mark("type-ident?");
        tp = G_int_type;
    }
    if(first->klass == Var) {
        parsize = tp->size;
        if(tp->form >= Array ) {
            S_mark("no struct params");
        }
    } else {
        parsize = R_WORD_SIZE;
    }
    obj = first;
    while(obj != guard) {
        obj->type = tp;
        *parblksize += parsize;
        obj = obj->next;
    }
}

static void procedure_decl(void) {
    G_Object *proc, *obj;
    S_Identifier procid;
    INTEGER locblksize, parblksize;

    S_get(&sym);
    if(sym == s_ident) {
        strcpy(procid, S_identifier);
        new_object(&proc, Proc);
        S_get(&sym);
        parblksize = G_MARK_SIZE;
        G_inc_level(1);
        open_scope();
        proc->value = -1;
        if(sym == s_lparen) {
            S_get(&sym);
            if(sym == s_rparen) {
                S_get(&sym);
            } else {
                procedure_decl_fp_section(&parblksize);
                while(sym == s_semicolon ) {
                    S_get(&sym);
                    procedure_decl_fp_section(&parblksize);
                }
                if(sym == s_rparen) {
                    S_get(&sym);
                } else {
                    S_mark(")?");
                }
            }
        }
        obj = top_scope->next;
        locblksize = parblksize;
        while(obj != guard) {
            obj->level = G_current_level;
            if(obj->klass == Par) {
                locblksize -= R_WORD_SIZE;
            } else {
                locblksize -= obj->type->size;
            }
            obj->value = locblksize;
            obj = obj->next;
        }
        proc->dsc = top_scope->next;
        if(sym == s_semicolon) {
            S_get(&sym);
        } else {
            S_mark(";?");
        }
        locblksize = 0;
        declarations(&locblksize);
        while(sym == s_procedure) {
            procedure_decl();
            if(sym == s_semicolon) {
                S_get(&sym);
            } else {
                S_mark(";?");
            }
        }
        proc->value = G_pc;
        G_enter(locblksize);
        if(sym == s_begin) {
            S_get(&sym);
            statement_sequence();
        }
        if(sym == s_end) {
            S_get(&sym);
        } else {
            S_mark("END?");
        }
        if(sym == s_ident) {
            if(strcmp(procid, S_identifier) != 0 ) {
                S_mark("no match");
            }
            S_get(&sym);
        } else {
            S_mark("ident?");
        }
        G_return(parblksize - G_MARK_SIZE);
        close_scope();
        G_inc_level(-1);
        ensure_not_null(proc);
        ensure_not_null(proc->dsc);
    }
}

static void module(void) {
    S_Identifier module_identifier;
    INTEGER varsize;

    if(sym == s_module) {
        S_get(&sym);
        G_open();
        open_scope();
        varsize = 0;
        if(sym == s_ident) {
            strcpy(module_identifier, S_identifier);
            S_get(&sym);
        } else {
            S_mark("ident?");
        }
        if(sym == s_semicolon) {
            S_get(&sym);
        } else {
            S_mark(";?");
        }
        declarations(&varsize);
        while(sym == s_procedure) {
            procedure_decl();
            if(sym == s_semicolon) {
                S_get(&sym);
            } else {
                S_mark(";?");
            }
        }
        G_header();
        if(sym == s_begin) {
            S_get(&sym);
            statement_sequence();
        }
        if(sym == s_end) {
            S_get(&sym);
        } else {
            S_mark("END?");
        }
        if(sym == s_ident) {
            if(strcmp(module_identifier, S_identifier) != 0) {
                S_mark("no match");
            }
            S_get(&sym);
        } else {
            S_mark("ident?");
        }
        if(sym != s_period) {
            S_mark(". ?");
        }
        close_scope();
        if(!S_error) {
            G_close(varsize);
        }
    } else {
        S_mark("MODULE?");
    }
    fix_foward_calls();
}

/*
Creates a object of the given class, name, value, and type, and adds it to the
topmost scope.
*/;
static void enter(G_ClassMode klass, INTEGER value, S_Identifier name, G_Type* type) {
    G_Object* obj = xcalloc(1, sizeof(G_Object));
    obj->klass = klass;
    obj->value = value;
    strcpy(obj->name, name);
    obj->type = type;
    obj->dsc = NULL;
    obj->next = top_scope->next;
    top_scope->next = obj;
}

static void init(void) {
    G_init();
    sym = s_null;
    guard = xcalloc(1, sizeof(G_Object));
    guard->klass = Var;
    guard->type = G_int_type;
    guard->value = 0;
    top_scope = NULL;
    open_scope();
    enter(Typ, 0, "UNDEFINED", G_undefined_type);
    enter(Typ, 1, "BOOLEAN", G_bool_type);
    enter(Typ, 2, "INTEGER", G_int_type);
    enter(Const, 1, "TRUE", G_bool_type);
    enter(Const, 0, "FALSE", G_bool_type);

    enter(StdProc, 1, "Read", NULL);
    enter(StdProc, 2, "Write", NULL);
    enter(StdProc, 3, "WriteHex", NULL);
    enter(StdProc, 4, "ReadByte", NULL);
    enter(StdProc, 5, "WriteByte", NULL);
    enter(StdProc, 6, "WriteLn", NULL);
    enter(StdProc, 7, "INC", NULL);
    enter(StdProc, 8, "DEC", NULL);
    enter(StdProc, 9, "ASSERT", NULL);
    universe = top_scope;
    forward_calls = NULL;
}

bool P_compile(char *filename, char *source_text, INTEGER** code, INTEGER* code_length, INTEGER* entry) {
    init();
    S_init(filename, source_text, 0);
    S_get(&sym);
    module();
    *code = G_code;
    *code_length = G_pc;
    *entry = G_entry;
    return !S_error;
}

