#include <limits.h>


/*@
requires INT_MIN <= x <= INT_MAX;
requires INT_MIN <= y <= INT_MAX;
ensures \result == x + y;
ensures (x > 0 && y > 0 && \result < 0) ==> \false; // overflow case
ensures (x < 0 && y < 0 && \result > 0) ==> \false; // underflow case
assigns \nothing;
*/
int add(int x, int y) {
    return x+y;
}

void foo() {
    int a = add(1, 43);
    int b = add(INT_MAX, INT_MAX);
}