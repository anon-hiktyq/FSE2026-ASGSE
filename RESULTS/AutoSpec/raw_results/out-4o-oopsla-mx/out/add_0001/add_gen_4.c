#include <limits.h>

/*@
requires INT_MIN <= x <= INT_MAX;
requires INT_MIN <= y <= INT_MAX;
ensures (\result == x + y) ==> (INT_MIN <= \result <= INT_MAX);
ensures (\result != x + y) ==> ((x > 0 && y > INT_MAX - x) || (x < 0 && y < INT_MIN - x));
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