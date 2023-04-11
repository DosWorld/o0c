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

#ifndef _GEN_H_
#define _GEN_H_

#define G_MAX_CODE 1000
#define G_MARK_SIZE (2 * R_WORD_SIZE)

typedef enum {
    Head = 0,
    Var = 1, Par = 2, Const = 3, Fld = 4, Typ = 5, Proc = 6, StdProc = 7,
    Reg = 10, Cond = 11
} G_ClassMode;

typedef enum { Undefined, Boolean, Integer, Array, Record } G_Form;

typedef struct G_Item G_Item;

typedef struct G_Object G_Object;

typedef struct G_Type G_Type;

struct G_Object {
    G_ClassMode klass;
    size_t level;
    G_Object* next;
    G_Object* dsc;
    G_Type* type;
    S_Identifier name;
    INTEGER value;
};

struct G_Item {
    G_ClassMode mode;
    size_t level;
    G_Type* type;
    INTEGER a;
    INTEGER b;
    INTEGER c;
    INTEGER r;
};

G_Item G_make_item(void);

struct G_Type {
    G_Form form;
    G_Object* fields;
    G_Type* base;
    size_t size;
    size_t len;
};

G_Type* G_new_type(G_Form form, size_t size);

extern G_Type* G_undefined_type;
extern G_Type* G_bool_type;
extern G_Type* G_int_type;
extern size_t G_current_level;
extern INTEGER G_pc;
extern INTEGER G_entry;
extern INTEGER G_code[G_MAX_CODE];
void G_print_item(G_Item* i);
void G_print_object(G_Object* o);
void G_print_type(G_Type* t);
void G_fix(INTEGER at, INTEGER with);
void G_fix_link(INTEGER L);
void G_inc_level(size_t n);
void G_make_const_item(/*out*/G_Item* x, G_Type* type, INTEGER value);
void G_item_from_object(/*out*/G_Item* x, /*in*/G_Object* y);
void G_field(/*inout*/G_Item* x, /*in*/G_Object* y);
void G_index(/*inout*/G_Item* x, /*in*/G_Item* y);
void G_op1(S_Symbol op, /*inout*/G_Item* x);
void G_op2(S_Symbol op, /*inout*/G_Item* x, /*in*/G_Item* y);
void G_relation(S_Symbol op, /*inout*/G_Item* x, /*in*/G_Item* y);
void G_store(/*inout*/G_Item* x, /*in*/G_Item* y);
void G_parameter(G_Item* x, G_Type* fp_type, G_ClassMode fp_class);
void G_cond_forward_jump(G_Item* x);
void G_backward_jump(INTEGER L);
void G_forward_jump(INTEGER* L);
void G_call(G_Item* x);
void G_io_read(G_Item* y);
void G_io_write(G_Item* y);
void G_io_write_hex(G_Item* y);
void G_io_read_byte(G_Item* y);
void G_io_write_byte(G_Item* y);
void G_io_write_line(void);
void G_inc_dec(char inc, G_Item* y, G_Item* delta);
void G_assert(G_Item* y);
void G_header(void);
void G_enter(INTEGER size);
void G_return(INTEGER size);
void G_open(void);
void G_close(INTEGER globals);
void G_init(void);

#endif

