#include <stdint.h>
#include <stdio.h>
#include "sat_add.h"

/* Independent, wider-arithmetic oracle; covers all 65,536 input pairs. */
int main(void) {
    for (unsigned x = 0; x < 256; ++x) {
        for (unsigned y = 0; y < 256; ++y) {
            const unsigned sum = x + y;
            const unsigned expected = sum > 255 ? 255 : sum;
            const unsigned actual = sat_add((uint8_t)x, (uint8_t)y);
            if (actual != expected) {
                fprintf(stderr, "mismatch at %u, %u: %u != %u\n",
                        x, y, actual, expected);
                return 1;
            }
        }
    }
    puts("PASS generated C: all 65536 unsigned-byte input pairs");
    return 0;
}
