/*
@author: Michael Rohs
@date: November 28, 2021
*/

#ifndef _UTIL_H_
#define _UTIL_H_

#include <stdlib.h>
#include <stdio.h>
#include <stdbool.h>
#include <string.h>

extern char *read_file(char* name);

#define Set long

Set make_set(void);
char in(int x, Set s);
void incl(Set* s, int x);
void excl(Set* s, int x);

#define ODD(x) ((x) & 1)
#define EVEN(x) !ODD(x)

#define require_not_null(argument)
#define require(description, condition)
#define ensure(description, condition)
#define assert(description, condition)
#define assert_not_null(pointer)
#define ensure_code(x)
#define ensure_not_null(pointer)

#define exists(i, length, condition) ({\
   bool _exists_result = false;\
   for (int i = 0; i < length; i++) { if (condition) { _exists_result = true; break; } }\
   _exists_result;\
})

#define exists_x(init, has_more_steps, do_step, condition) ({\
   bool _exists_result = false;\
   for (init; has_more_steps; do_step) { if (condition) { _exists_result = true; break; } }\
   _exists_result;\
})

#define panic(message) {\
    fprintf(stderr, "%s:%d, %s: %s\n", __FILE__, __LINE__, __func__, message);\
    exit(EXIT_FAILURE);\
}

#define panicf(...) {\
    fprintf(stderr, "%s:%d, %s: ", __FILE__, __LINE__, __func__);\
    fprintf(stderr, __VA_ARGS__);\
    fprintf(stderr, "\n");\
    exit(EXIT_FAILURE);\
}

#define panic_if(condition, message) \
if (condition) {\
    fprintf(stderr, "%s:%d, %s: %s\n", __FILE__, __LINE__, __func__, message);\
    exit(EXIT_FAILURE);\
}

#define panicf_if(condition, ...) \
if (condition) {\
    fprintf(stderr, "%s:%d, %s: ", __FILE__, __LINE__, __func__);\
    fprintf(stderr, __VA_ARGS__);\
    fprintf(stderr, "\n");\
    exit(EXIT_FAILURE);\
}

#define exit_if(condition, ...) \
if (condition) {\
    fprintf(stderr, __VA_ARGS__);\
    fprintf(stderr, "\n");\
    exit(EXIT_FAILURE);\
}

#define xcalloc(count, size) calloc(count , size)
#define xmalloc(size) malloc(size)

#endif

