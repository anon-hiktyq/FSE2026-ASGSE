#include <limits.h>

/*@
requires x >= INT_MIN && y >= INT_MIN && x <= INT_MAX && y <= INT_MAX;
requires x <= INT_MAX - y;
requires INT_MIN <= y <= INT_MAX;
requires INT_MIN <= x <= INT_MAX;
requires (y >= 0 && x <= INT_MAX - y) || (y < 0 && x >= INT_MIN - y); // No overflow;
requires (x >= 0 && y >= 0 ==> x + y <= INT_MAX) && (x < 0 && y < 0 ==> x + y >= INT_MIN);
requires (x >= 0 && y >= 0 && x <= INT_MAX - y) || (x < 0 && y < 0 && x >= INT_MIN - y) || (x >= 0 && y < 0) || (x < 0 && y >= 0);
requires (x > 0 && y > 0 ==> x + y <= INT_MAX) && (x < 0 && y < 0 ==> x + y >= INT_MIN);
requires (long)x + (long)y <= INT_MAX && (long)x + (long)y >= INT_MIN;
requires ((y >= 0) ==> (x <= INT_MAX - y)) && ((y < 0) ==> (x >= INT_MIN - y));
ensures \result == x + y;
ensures (\result == x + y) ==> (INT_MIN <= \result <= INT_MAX);
ensures (\result != x + y) ==> ((x > 0 && y > INT_MAX - x) || (x < 0 && y < INT_MIN - x));
assigns \nothing;
*/
int add(int x, int y) {
    return x+y;
}

void foo() {
    int a = add(1, 43);
    //@ assert a == 44;
    int b = add(INT_MAX, INT_MAX);
}