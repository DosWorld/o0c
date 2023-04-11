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

/*
All instructions of the RISC processor are 32 bits long. There are four formats:
- F0: 00 op[4] a[4] b[4] unused[14] c[4]
- F1: 01 op[4] a[4] b[4] im[18]
- F2: 10 op[4] a[4] b[4] disp[18]
- F3: 11 op[4] disp[26]
where a, b, and c refer to registers (R0-R15) and im and disp are 18-bit
immediate values. The opcodes occupy the upper 6 bits of the instruction, so
there can be at most 64 instructions.
*/

#define NAME(opc) {opc, #opc}

struct {
    R_Opcode opc;
    char *name;
} opcode_names[] = {
    NAME(MOV), NAME(MVN), NAME(ADD), NAME(SUB), NAME(MUL), NAME(Div), NAME(Mod), NAME(CMP),
    NAME(MOVI), NAME(MVNI), NAME(ADDI), NAME(SUBI), NAME(MULI), NAME(DIVI),
    NAME(MODI), NAME(CMPI), NAME(CHKI),
    NAME(LDW), NAME(LDB), NAME(POP), NAME(STW), NAME(STB), NAME(PSH),
    NAME(RD), NAME(WRD), NAME(WRH), NAME(WRL), NAME(RB), NAME(WRB),
    NAME(BEQ), NAME(BNE), NAME(BLT), NAME(BGE), NAME(BLE), NAME(BGT), NAME(BR),
    NAME(BSR), NAME(RET)
};
#define R_OPCODE_COUNT (sizeof(opcode_names) / sizeof(opcode_names[0]))

static INTEGER IR;
static BOOLEAN N, Z;
static INTEGER R[16];
static INTEGER M[R_MEM_SIZE / R_WORD_SIZE];

#define ASH(x, s) ((x) << (s))

INTEGER R_mod(INTEGER x, INTEGER y) {
    require("valid divisor", y != 0);
    x = x % y;
    if(y < 0 ) {
        y = -y;
    }
    while(x < 0 ) {
        x += y;
    }
    ensure("valid remainder", 0 <= x && x < y);
    return x;
}

static INTEGER get_M(INTEGER i) {
    exit_if(i < 0 || i >= R_MEM_SIZE / R_WORD_SIZE, "invalid word address (%d)", i);

    return M[i];
}

static INTEGER get_B(INTEGER i) {
    char *B;
    exit_if(i < 0 || i >= R_MEM_SIZE, "invalid byte address (%d)", i);
    B = (char*)M;
    return B[i] & 0xff;
}

static void set_M(INTEGER i, INTEGER x) {
    exit_if(i < 0 || i >= R_MEM_SIZE / R_WORD_SIZE, "invalid word address (%d)", i);
    M[i] = x;
}

static void set_B(INTEGER i, INTEGER x) {
    char *B;
    exit_if(i < 0 || i >= R_MEM_SIZE, "invalid byte address (%d)", i);
    B = (char*)M;
    B[i] = x;
}

void R_decode_instruction(INTEGER x, INTEGER* opc, INTEGER* a, INTEGER* b, INTEGER* c) {
    *opc = (x >> 26) & 0x3f;
    *a = (x >> 22) & 0xf;
    *b = (x >> 18) & 0xf;
    if(*opc < MOVI ) {
        *c = x & 0xf;
    } else if(*opc < BEQ ) {
        *c = x & 0x3ffff;
        if(*c >= 0x20000 ) {
            *c -= 0x40000;
        }
    } else {
        *c = x & 0x3ffffff;
        if(*c >= 0x2000000 ) {
            *c -= 0x4000000;
        }
    }
}

void R_print_instruction(INTEGER x) {
    INTEGER opc, a, b, c;
    char* opc_name;
    INTEGER i;
    R_decode_instruction(x, &opc, &a, &b, &c);
    opc_name = "?";
    for(i = 0; i < R_OPCODE_COUNT; i++ ) {
        if(opcode_names[i].opc == opc ) {
            opc_name = opcode_names[i].name;
            break;
        }
    }
    if(opc < MOVI ) {
        printf("%-4s %2d %2d %2d\n", opc_name, a, b, c);
    } else if(opc < BEQ ) {
        printf("%-4s %2d %2d %2d\n", opc_name, a, b, c);
    } else {
        printf("%-4s %2d\n", opc_name, c);
    }
}

/*
Encodes an instruction according to the given format. Negative values for c have
to be limited to 4 bits (F0), 18 bits (F1 and F2), or 26 (F3) bits.
*/
INTEGER R_encode_instruction(INTEGER opc, INTEGER a, INTEGER b, INTEGER c) {
    INTEGER i;
    exit_if(opc < 0 || opc > RET, "opc out of range (%d)", opc);
    exit_if(a < 0 || a > 0xf, "a out of range (%d)", a);
    exit_if(b < 0 || b > 0xf, "b out of range (%d)", b);
    opc &= 0x3f;
    a &= 0xf;
    b &= 0xf;
    if(opc < MOVI ) {
        exit_if(c < 0 || c > 0xf, "c out of range (%d), F0", c);
        c &= 0xf;
    } else if(opc < BEQ ) {
        exit_if(c < -0x20000 || c > 0x1ffff, "c out of range (%d), F1 or F2", c);
        c &= 0x3ffff;
    } else {
        exit_if(a != 0, "a != 0 (%d), F3", a);
        exit_if(b != 0, "b != 0 (%d), F3", b);
        exit_if(c < -0x2000000 || c >= 0x2000000, "c out of range (%d), F3", c);
        a = 0;
        b = 0;
        c &= 0x3ffffff;
    }
    i = (opc << 26) | (a << 22) | (b << 18) | c;

    return i;
}

/*
Executes code starting at the given start address. The start address is given in
bytes relative to the code origin. The code must have been loaded into memory
before.
*/
void R_execute(INTEGER start) {
    INTEGER opc, a, b, c, nextPC;

    require("valid start", start >= 0
            && R_PROG_ORG + start + R_WORD_SIZE <= R_MEM_SIZE
            && (start & 0x3) == 0);
    R[14] = 0;
    R[15] = start + R_PROG_ORG;

    while(1) {
        nextPC = R[15] + R_WORD_SIZE;
        exit_if(R[15] < 0 || R[15] > R_MEM_SIZE - R_WORD_SIZE || (R[15] & 0x3) != 0,
                "invalid PC (%d)", R[15]);
        IR = M[R[15] / R_WORD_SIZE];
        R_decode_instruction(IR, &opc, &a, &b, &c);
        if(opc < MOVI ) {
            c = R[c & 0xf];
        }
        switch(opc ) {
        case MOV:
        case MOVI:
            R[a] = ASH(c, b);
            break;
        case MVN:
        case MVNI:
            R[a] = -ASH(c, b);
            break;
        case ADD:
        case ADDI:
            R[a] = R[b] + c;
            break;
        case SUB:
        case SUBI:
            R[a] = R[b] - c;
            break;
        case MUL:
        case MULI:
            R[a] = R[b] * c;
            break;
        case Div:
        case DIVI:
            R[a] = R[b] / c;
            break;
        case Mod:
        case MODI:
            R[a] = R_mod(R[b], c);
            break;
        case CMP:
        case CMPI:
            Z = R[b] == c;
            N = R[b] < c;
            break;
        case CHKI:
            exit_if(R[a] < 0 || R[a] >= c, \
                    "CHKI failed (%d, %d)", c, R[a]);
            break;
        case LDW:
            R[a] = get_M((R[b] + c) / R_WORD_SIZE);
            break;
        case LDB:
            R[a] = get_B(R[b] + c);
            break;
        case POP:
            R[a] = get_M((R[b]) / R_WORD_SIZE);
            R[b] += c;
            break;
        case STW:
            set_M((R[b] + c) / R_WORD_SIZE, R[a]);
            break;
        case STB:
            set_B(R[b] + c, R[a]);
            break;
        case PSH:
            R[b] -= c;
            set_M(R[b] / R_WORD_SIZE, R[a]);
            break;
        case RD:
            scanf("%d", &R[a]);
            break;
        case WRD:
            printf(" %d", R[c]);
            break;
        case WRH:
            printf(" %xH", R[c]);
            break;
        case WRL:
            printf("\n");
            break;
        case RB:
            R[a] = getchar();
            break;
        case WRB:
            putchar(R[c]);
            break;
        case BEQ:
            if(Z ) {
                nextPC = R[15] + c * R_WORD_SIZE;
            }
            break;
        case BNE:
            if(!Z ) {
                nextPC = R[15] + c * R_WORD_SIZE;
            }
            break;
        case BLT:
            if(N ) {
                nextPC = R[15] + c * R_WORD_SIZE;
            }
            break;
        case BGE:
            if(!N ) {
                nextPC = R[15] + c * R_WORD_SIZE;
            }
            break;
        case BLE:
            if(Z || N ) {
                nextPC = R[15] + c * R_WORD_SIZE;
            }
            break;
        case BGT:
            if(!Z && !N ) {
                nextPC = R[15] + c * R_WORD_SIZE;
            }
            break;
        case BR:
            nextPC = R[15] + c * R_WORD_SIZE;
            break;
        case BSR:
            nextPC = R[15] + c * R_WORD_SIZE;
            R[14] = R[15] + R_WORD_SIZE;
            break;
        case RET:
            nextPC = R[c & 0xf];
            break;
        default:
            exit_if(true, "invalid opcode (%d)", opc);
        };
        if(nextPC == 0 ) {
            break;
        }
        R[15] = nextPC;
    };
}

/*
Loads the code words into memory. The length refers to the number of code words
(not bytes).
*/
void R_load(INTEGER* code, INTEGER len) {
    INTEGER i;
    require_not_null(code);
    require("valid length", len >= 0 && R_PROG_ORG + R_WORD_SIZE * len <= R_MEM_SIZE);
    for(i = 0; i < len; i++ ) {
        M[i + R_PROG_ORG / R_WORD_SIZE] = code[i];
    }
}

void R_print_code(INTEGER* code, INTEGER len) {
    INTEGER i;
    require_not_null(code);
    require("not negative", len >= 0);
    for(i = 0; i < len; i++ ) {
        printf("%3ld ", i);
        R_print_instruction(code[i]);
    }
}

/*
Prints memory from start index to end index (end is exclusive) in rows of the
given length.
*/
void R_print_memory(int from, int to, int row_length) {
    int i, j;
    if(from < 0 ) {
        from = 0;
    }
    if(to > R_MEM_SIZE ) {
        to = R_MEM_SIZE;
    }
    if(row_length < 1 ) {
        row_length = 1;
    }
    i = from;
    while(i < to ) {
        assert("valid index", 0 <= i && i < R_MEM_SIZE);
        for(j = 0; j < row_length; j++ ) {
            printf("%4ld: %6ld ", i, M[i]);
            i++;
            if(i >= to ) {
                break;
            }
        }
        printf("\n");
    }
}

