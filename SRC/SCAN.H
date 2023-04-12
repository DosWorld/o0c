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
extern bool S_error;

void S_line_and_column(int* line, int* column);
void S_mark(const char* msg);
void S_get(S_Symbol* sym);
void S_init(char *filename, char *a_source_text, int pos);

#endif

