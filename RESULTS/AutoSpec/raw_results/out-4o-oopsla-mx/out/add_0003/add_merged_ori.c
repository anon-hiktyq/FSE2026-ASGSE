#include <limits.h>

/*@
requires y >= INT_MIN && y <= INT_MAX;
requires y <= INT_MAX - x;;
requires x >= INT_MIN && x <= INT_MAX;
requires x <= INT_MAX - y;;
requires x <= INT_MAX - y;
requires INT_MIN <= y <= INT_MAX;
requires INT_MIN <= y <= INT_MAX - x;
requires INT_MIN <= x <= INT_MAX;
requires INT_MIN <= x <= INT_MAX - y;;
requires INT_MIN <= x <= INT_MAX && INT_MIN <= y <= INT_MAX;
requires (x >= 0 && y >= 0 && x <= INT_MAX - y) || (x < 0 && y < 0 && x >= INT_MIN - y);
ensures \result == x + y;
ensures INT_MIN <= \result <= INT_MAX;
ensures (x > 0 && y > INT_MAX - x) || (x < 0 && y < INT_MIN - x) ==> \result == x + y;
ensures (x > 0 && y > 0 && \result < 0) ==> \false; // Overflow check for positive numbers;
ensures (x < 0 && y < 0 && \result > 0) ==> \false; // Overflow check for negative numbers;
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