#include <limits.h>


/*@
requires x >= INT_MIN && x <= INT_MAX;
requires y >= INT_MIN && y <= INT_MAX;
ensures \result >= INT_MIN && \result <= INT_MAX;
ensures (x > 0 && y > 0) ==> \result > 0;
ensures (x < 0 && y < 0) ==> \result < 0;
ensures (x > 0 && y < 0) || (x < 0 && y > 0) ==> \result != 0;
assigns \nothing;
*/
int add(int x, int y) {
    return x+y;
}

void foo() {
    int a = add(1, 43);
    int b = add(INT_MAX, INT_MAX);
}