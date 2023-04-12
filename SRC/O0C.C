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
#include "PARSER.H"

char* filename;
INTEGER code_length;
INTEGER entry;
INTEGER* code;
char *source_text;

char *basename(char *n) {
        int i;
        i = 0;
        while(n[i] != 0) {
                i++;
        }
        while((i >= 0) && (n[i] != '\\') && (n[i] != '/')) {
                i--;
        }
        i++;
        return n + i;
}

int main(int argc, char* argv[]) {
    if(argc != 2 ) {
        printf("Usage: %s <filename source file>\n", basename(argv[0]));
        exit(EXIT_FAILURE);
    }
    filename = argv[1];
    source_text = read_file(filename);
    if(P_compile(filename, source_text, &code, &code_length, &entry) ) {
        R_print_code(code, code_length);
        R_load(code, code_length);
        printf("RISC OUTPUT BEGIN\n");
        R_execute(entry * R_WORD_SIZE);
        printf("RISC OUTPUT END\n");
    }
    return 0;
}
