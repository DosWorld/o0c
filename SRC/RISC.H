#ifndef _RISC_H_
#define _RISC_H_

#define R_MEM_SIZE 4096
#define R_PROG_ORG 2048
#define R_WORD_SIZE 4

typedef enum {
    
    MOV = 0, MVN = 1, ADD = 2, SUB = 3, MUL = 4, Div = 5, Mod = 6, CMP = 7,
    
    MOVI = 16, MVNI = 17, ADDI = 18, SUBI = 19, MULI = 20, DIVI = 21,
    MODI = 22, CMPI = 23, CHKI = 24,
    
    LDW = 32, LDB = 33, POP = 34, STW = 36, STB = 37, PSH = 38,
    RD = 40, WRD = 41, WRH = 42, WRL = 43, RB = 44, WRB = 45,
    
    BEQ = 48, BNE = 49, BLT = 50, BGE = 51, BLE = 52, BGT = 53, BR = 56,
    BSR = 57, RET = 58
} R_Opcode;

typedef int32_t INTEGER;
typedef bool BOOLEAN;
#define INTEGER_MAX INT32_MAX

INTEGER R_mod(INTEGER x, INTEGER y);
void R_decode_instruction(INTEGER x, INTEGER* opc, INTEGER* a, INTEGER* b, INTEGER* c);
void R_print_instruction(INTEGER x);
INTEGER R_encode_instruction(INTEGER opc, INTEGER a, INTEGER b, INTEGER c);
void R_execute(INTEGER start);
void R_load(INTEGER* code, INTEGER len);
void R_print_code(INTEGER* code, INTEGER len);
void R_print_memory(int from, int to, int row_length);

#endif

