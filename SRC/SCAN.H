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

#ifndef _SCAN_H_
#define _SCAN_H_

#define S_IDENTIFIER_LENGTH 32

typedef enum {
    s_null = 0,
    s_times = 1, s_div = 3, s_mod = 4, s_and = 5,
    s_plus = 6, s_minus = 7, s_or = 8,
    s_eql = 9, s_neq = 10, s_lss = 11, s_geq = 12, s_leq = 13, s_gtr = 14,
    s_period = 18, s_comma = 19, s_colon = 20,
    s_rparen = 22, s_rbrak = 23, s_of = 25, s_then = 26, s_do = 27,
    s_lparen = 29, s_lbrak = 30, s_not = 32, s_becomes = 33,
    s_number = 34, s_ident = 37, s_semicolon = 38,
    s_end = 40, s_else = 41, s_elsif = 42, s_if = 44, s_while = 46,
    s_array = 54, s_record = 55, s_const = 57, s_type = 58, s_var = 59,
    s_procedure = 60, s_begin = 61, s_module = 63,
    s_eof = 64
} S_Symbol;

typedef char S_Identifier[S_IDENTIFIER_LENGTH + 1];

extern INTEGER S_value;
extern S_Identifier S_identifier;
extern char S_error;

void S_line_and_column(int* line, int* column);
void S_mark(const char* msg);
void S_get(S_Symbol* sym);
void S_init(char *a_source_text, int pos);

#endif

