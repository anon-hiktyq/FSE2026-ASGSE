#include <limits.h>


/*@
requires y >= INT_MIN && y <= INT_MAX;
requires x >= INT_MIN && x <= INT_MAX;
requires INT_MIN <= y <= INT_MAX;
requires INT_MIN <= x <= INT_MAX;
ensures \result >= INT_MIN && \result <= INT_MAX;
ensures \result == x + y;;
ensures \result == x + y;
ensures INT_MIN <= \result <= INT_MAX;
ensures (x > 0 && y > 0) ==> \result > 0;
ensures (x > 0 && y > 0 ==> \result > 0);
ensures (x > 0 && y > 0 && \result < 0) ==> \false; // overflow case;
ensures (x > 0 && y > 0 && \result < 0) ==> \false; // Overflow for positive addition;
ensures (x > 0 && y < 0) || (x < 0 && y > 0) ==> \result != 0;
ensures (x > 0 && y < 0) ==> \result <= x;
ensures (x > 0 && y < 0 ==> \result >= INT_MIN);
ensures (x < 0 && y > 0) ==> \result >= y;
ensures (x < 0 && y > 0 ==> \result <= INT_MAX);
ensures (x < 0 && y < 0) ==> \result < 0;
ensures (x < 0 && y < 0 ==> \result < 0);
ensures (x < 0 && y < 0 && \result > 0) ==> \false; // underflow case;
ensures (x < 0 && y < 0 && \result > 0) ==> \false; // Underflow for negative addition;
assigns \nothing;
*/
int add(int x, int y) {
    return x+y;
}

void foo() {
    int a = add(1, 43);
    int b = add(INT_MAX, INT_MAX);
}