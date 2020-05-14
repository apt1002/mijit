#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

struct Buffer;

extern struct Buffer *mijit_new(void);
extern void mijit_drop(struct Buffer *b);
extern int64_t five();

int main(void) {
    struct Buffer *b = mijit_new();
    if (!b) { exit(1); }
    printf("%ld\n", five());
    mijit_drop(b);
}
