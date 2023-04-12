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

#include <stdio.h>
#include <string.h>
#include <stdint.h>
#include <ctype.h>
#include <limits.h>

#include "UTIL.H"
#include "RISC.H"
#include "SCAN.H"

#define NAME(sym) {sym, #sym}

struct {
    S_Symbol sym;
    char* name;
} symbol_names[] = {
    NAME(s_null),
    NAME(s_times), NAME(s_div), NAME(s_mod), NAME(s_and),
    NAME(s_plus), NAME(s_minus), NAME(s_or),
    NAME(s_eql), NAME(s_neq), NAME(s_lss), NAME(s_geq), NAME(s_leq), NAME(s_gtr),
    NAME(s_period), NAME(s_comma), NAME(s_colon),
    NAME(s_rparen), NAME(s_rbrak), NAME(s_of), NAME(s_then), NAME(s_do),
    NAME(s_lparen), NAME(s_lbrak), NAME(s_not), NAME(s_becomes),
    NAME(s_number), NAME(s_ident), NAME(s_semicolon),
    NAME(s_end), NAME(s_else), NAME(s_elsif), NAME(s_if), NAME(s_while),
    NAME(s_array), NAME(s_record), NAME(s_const), NAME(s_type), NAME(s_var),
    NAME(s_procedure), NAME(s_begin), NAME(s_module),
    NAME(s_eof)
};
#define S_SYMBOL_COUNT (sizeof(symbol_names) / sizeof(symbol_names[0]))

struct {
    S_Symbol sym;
    const char* id;
} keyword_table[] = {
    {s_null, "BY"},
    {s_do, "DO"},
    {s_if, "IF"},
    {s_null, "IN"},
    {s_null, "IS"},
    {s_of, "OF"},
    {s_or, "OR"},
    {s_null, "TO"},
    {s_end, "END"},
    {s_null, "FOR"},
    {s_mod, "MOD"},
    {s_null, "NIL"},
    {s_var, "VAR"},
    {s_null, "CASE"},
    {s_else, "ELSE"},
    {s_null, "EXIT"},
    {s_then, "THEN"},
    {s_type, "TYPE"},
    {s_null, "WITH"},
    {s_array, "ARRAY"},
    {s_begin, "BEGIN"},
    {s_const, "CONST"},
    {s_elsif, "ELSIF"},
    {s_null, "IMPORT"},
    {s_null, "UNTIL"},
    {s_while, "WHILE"},
    {s_record, "RECORD"},
    {s_null, "REPEAT"},
    {s_null, "RETURN"},
    {s_null, "POINTER"},
    {s_procedure, "PROCEDURE"},
    {s_div, "DIV"},
    {s_null, "LOOP"},
    {s_module, "MODULE"},
};
#define KEYWORD_COUNT (sizeof(keyword_table) / sizeof(keyword_table[0]))

INTEGER S_value;
S_Identifier S_identifier;
char S_error = 1;
static char ch;
static int errpos;
static char * source_text;
static size_t source_text_pos;
static size_t source_text_pos_token;

#define ORD(ch) ((ch) & 0xff)

void S_line_and_column(int* line, int* column) {
    int i;
    *line = 1;
    *column = 1;
    for(i = 0; i < source_text_pos_token && (source_text[i] != 0); i++ ) {
        char c = source_text[i];
        if(c == '\n' ) {
            *line += 1;
            *column = 1;
        } else {
            *column += 1;
        }
    }
}

/*
Outputs a message referring to the current scanner position. The position is the
byte offset from the start of the source text. Only a single message per
position is output.
*/
void S_mark(const char* msg) {
    int line, column;
    S_error = 1;
    if(source_text_pos_token >= errpos ) {
        S_line_and_column(&line, &column);
        fprintf(stderr, "\t%d:%d: %s\n", line, column, msg);
        errpos = source_text_pos + 5;
    }
}

static void print_symbol(S_Symbol sym) {
    int i;
    char* sym_name = "s_unknown";
    for(i = 0; i < S_SYMBOL_COUNT; i++ ) {
        if(symbol_names[i].sym == sym ) {
            sym_name = symbol_names[i].name;
            break;
        }
    }
    printf("sym = %d %s, val = %d, id = %s\n", sym, sym_name + 2,
           S_value, S_identifier);
}

/*
Reads the next character from the source text, or '\0' if the end has been
reached.
*/;
static void read(char* c) {
    *c = 0;
    if(source_text[source_text_pos] != 0) {
        *c = source_text[source_text_pos];
        source_text_pos++;
    }
}

static char read_eot() {
    return source_text[source_text_pos] == 0;
}

/*
Reads an identifier. Assumes that the first character has already been read.
Also checks if the identifier is a keyword and sets the symbol correspondingly
(or to s_ident if the identifier is not a keyword).
*/
static void identifier(S_Symbol* sym) {
    int i = 0, k;
    do {
        if(i < S_IDENTIFIER_LENGTH ) {
            S_identifier[i++] = ch;
        }
        read(&ch);
    } while ((ch >= '0' && ch <= '9') || (toupper(ch) >= 'A' && toupper(ch) <= 'Z'));
    S_identifier[i] = '\0';
    if(i >= S_IDENTIFIER_LENGTH ) {
        S_mark("identifier too long");
    }

    k = 0;
    while(k < KEYWORD_COUNT && strcmp(S_identifier, keyword_table[k].id) != 0 ) {
        k++;
    }
    if(k < KEYWORD_COUNT ) {
        *sym = keyword_table[k].sym;
    } else {
        *sym = s_ident;
    }
}

static void number(S_Symbol* sym) {
    char too_large = 0;
    S_value = 0;
    *sym = s_number;
    do {
        if(S_value <= (INTEGER_MAX - ORD(ch) + ORD('0')) / 10 ) {
            S_value = 10 * S_value + (ORD(ch) - ORD('0'));
        } else {
            too_large = 1;
        }
        read(&ch);
    } while (ch >= '0' && ch <= '9');
    if(too_large ) {
        S_mark("number too large");
        S_value = 0;
    }
}

static void comment(S_Symbol* sym) {
    read(&ch);
    while (1) {
        while (1) {
            while(ch == '(' ) {
                read(&ch);
                if(ch == '*' ) {
                    comment(sym);
                }
            }
            if(ch == '*' ) {
                read(&ch);
                break;
            }
            if(read_eot() ) {
                break;
            }
            read(&ch);
        }
        if(ch == ')' ) {
            read(&ch);
            break;
        }
        if(read_eot() ) {
            S_mark("comment not terminated");
            break;
        }
    }
}

void S_get(S_Symbol* sym) {
    while(!read_eot() && ch <= ' ' ) {
        read(&ch);
    }
    source_text_pos_token = source_text_pos - 1;
    if(read_eot() ) {
        *sym = s_eof;
    } else {
        switch(ch ) {
        case '&':
            read(&ch);
            *sym = s_and;
            break;
        case '*':
            read(&ch);
            *sym = s_times;
            break;
        case '+':
            read(&ch);
            *sym = s_plus;
            break;
        case '-':
            read(&ch);
            *sym = s_minus;
            break;
        case '=':
            read(&ch);
            *sym = s_eql;
            break;
        case '#':
            read(&ch);
            *sym = s_neq;
            break;
        case '<': {
            read(&ch);
            if(ch == '=' ) {
                read(&ch);
                *sym = s_leq;
            } else {
                *sym = s_lss;
            }
            break;
        }
        case '>': {
            read(&ch);
            if(ch == '=' ) {
                read(&ch);
                *sym = s_geq;
            } else {
                *sym = s_gtr;
            }
            break;
        }
        case ';':
            read(&ch);
            *sym = s_semicolon;
            break;
        case ',':
            read(&ch);
            *sym = s_comma;
            break;
        case ':': {
            read(&ch);
            if(ch == '=' ) {
                read(&ch);
                *sym = s_becomes;
            } else {
                *sym = s_colon;
            }
            break;
        }
        case '.':
            read(&ch);
            *sym = s_period;
            break;
        case '(': {
            read(&ch);
            if(ch == '*' ) {
                comment(sym);

                S_get(sym);
            } else {
                *sym = s_lparen;
            }
            break;
        }
        case ')':
            read(&ch);
            *sym = s_rparen;
            break;
        case '[':
            read(&ch);
            *sym = s_lbrak;
            break;
        case ']':
            read(&ch);
            *sym = s_rbrak;
            break;
        case '~':
            read(&ch);
            *sym = s_not;
            break;
        default:
            if((ch >= '0') && (ch <= '9')) {
                number(sym);
            } else if(((ch >= 'a') && (ch <= 'z')) ||
                      ((ch >= 'A') && (ch <= 'Z'))) {
                identifier(sym);
            } else {
                read(&ch);
                *sym = s_null;
            }
            break;
        };
    }
}

/*
Initializes the scanner and prepares it to scan the source text starting at the
given position.
*/
void S_init(char *a_source_text, int pos) {
    source_text = a_source_text;
    source_text_pos = pos;
    source_text_pos_token = pos;
    S_value = 0;
    S_identifier[0] = '\0';
    ch = '\0';
    S_error = 0;
    errpos = pos;
    read(&ch);
}

