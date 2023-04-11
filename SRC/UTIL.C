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

String make_string2(char* s, int len) {
    String r;
    require_not_null(s);
    require("length not negative", len >= 0);
    r.s = s;
    r.len = len;
    r.cap = len;
    return r;
}

/**
Reads the contents of a file into a string The function fails if the file does
not exist or cannot be read.
@param[in] name file name (including path)
@return a string that points to a newly allocated char* with data read from file
*/
String read_file(char* name) {
    FILE *f;
    long size, sizeRead;
    char *s;

    require_not_null(name);

    // Opening in text mode should remove \r and only leave \n.
    // However, it does not do so on macOS.
    f = fopen(name, "r");
    panicf_if(f == NULL, "Cannot open %s", name);

    fseek (f, 0, SEEK_END);
    size = ftell(f);
    rewind(f);

    s = (char *)xmalloc(size + 1);
    sizeRead = fread(s, 1, size, f);
    // assert: size >= sizeRead (> if file contains \r characters)
    // printf("size = %lu, sizeRead = %lu, feof = %d\n", size, sizeRead, feof(f));
    panicf_if(sizeRead < size && feof(f) == 0, "Cannot read %s to end.\n", name);
    s[sizeRead] = '\0';

    fclose(f);
    return make_string2(s, sizeRead);
}

void write_file(char* name, String data) {
    FILE *f;
    size_t n_written;
    require_not_null(name);

    f = fopen(name, "w");
    panicf_if(f == NULL, "Cannot open %s", name);

    n_written = fwrite(data.s, 1, data.len, f);
    fclose(f);
    panicf_if(n_written != data.len, "Cannot write data to file %s.", name);
}

Set make_set(void) {
    return 0;
}

// Checks if x is in s.
bool in(int x, Set s) {
    require("valid range", 0 <= x && x < 64);
    return (s >> x) & 1;
}

// Adds x to s.
void incl(Set* s, int x) {
    require("valid range", 0 <= x && x < 64);
    s[0] |= (1 << x);
}

// Remooves x from s.
void excl(Set* s, int x) {
    require("valid range", 0 <= x && x < 64);
    s[0] &= ~(1 << x);
}


