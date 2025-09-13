#include <limits.h>

/*@
requires x >= INT_MIN && x <= INT_MAX;
requires y >= INT_MIN && y <= INT_MAX;
ensures \result == x + y;
ensures (x > 0 && y > 0 && \result < 0) ==> \false; // Overflow check for positive numbers
ensures (x < 0 && y < 0 && \result > 0) ==> \false; // Overflow check for negative numbers
assigns \nothing;
*/
int add(int x, int y) {
    return x+y;
}

void foo() {
    int a = add(1, 43);
    // @ assert a == 44;
    int b = add(INT_MAX, INT_MAX);
}