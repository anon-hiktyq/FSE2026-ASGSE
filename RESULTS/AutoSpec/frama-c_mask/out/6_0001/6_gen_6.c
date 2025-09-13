#include <limits.h>


/*@
requires INT_MIN <= x <= INT_MAX;
requires INT_MIN <= y <= INT_MAX;
ensures INT_MIN <= \result <= INT_MAX;
ensures \result == x + y;
assigns \nothing;
*/
int add(int x, int y) {
    return x+y;
}

void foo() {
    int a = add(1, 43);
    int b = add(INT_MAX, INT_MAX);
}