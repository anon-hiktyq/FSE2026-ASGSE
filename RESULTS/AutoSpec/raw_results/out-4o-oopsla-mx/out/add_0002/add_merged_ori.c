#include <limits.h>

/*@
requires x <= INT_MAX - y;
requires INT_MIN <= y <= INT_MAX;
requires INT_MIN <= x <= INT_MAX;
requires (x >= INT_MIN && x <= INT_MAX) && (y >= INT_MIN && y <= INT_MAX);
requires (x >= 0 && y >= 0 ==> x + y >= x && x + y >= y && x + y <= INT_MAX);
requires (x >= 0 && y >= 0 && x <= INT_MAX - y) || (x < 0 && y < 0 && x >= INT_MIN - y) || (x >= 0 && y < 0) || (x < 0 && y >= 0);
requires (x >= 0 && y <= INT_MAX - x) || (x < 0 && y >= INT_MIN - x); // No overflow;
requires (x > 0 && y > 0 ==> x + y > x && x + y > y) && (x < 0 && y < 0 ==> x + y < x && x + y < y);
requires (long)x + (long)y >= INT_MIN; // prevent underflow;
requires (long)x + (long)y <= INT_MAX; // prevent overflow;
requires ((y > 0) ==> (x <= INT_MAX - y)) && ((y < 0) ==> (x >= INT_MIN - y));
ensures \result == x + y;
ensures (x > 0 && y > 0 && x + y < x) ==> \false; // No overflow for positive values;
ensures (x < 0 && y < 0 && x + y > x) ==> \false; // No overflow for negative values;
assigns \nothing;
&& (x < 0 && y < 0 ==> x + y <= x && x + y <= y && x + y >= INT_MIN);
*/
int add(int x, int y) {
    return x+y;
}

void foo() {
    int a = add(1, 43);
    // @ assert a == 44;
    int b = add(INT_MAX, INT_MAX);
}