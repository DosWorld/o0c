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

#include "UTIL.H"

char *read_file(char* name) {
    FILE *f;
    long size, sizeRead;
    char *s;

    panicf_if((f = fopen(name, "r")) == NULL, "Cannot open %s", name);

    fseek (f, 0, SEEK_END);
    size = ftell(f);
    rewind(f);

    s = (char *)xmalloc(size + 1);
    sizeRead = fread(s, 1, size, f);
    s[sizeRead] = 0;

    fclose(f);
    return s;
}

Set make_set(void) {
    return 0;
}

char in(int x, Set s) {
    return (s >> x) & 1;
}

void incl(Set* s, int x) {
    *s |= (1 << x);
}

void excl(Set* s, int x) {
    *s &= ~(1 << x);
}


