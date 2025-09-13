#include <limits.h>

/*@
requires x >= INT_MIN && y >= INT_MIN && x <= INT_MAX && y <= INT_MAX;
requires (x > 0 && y > 0 ==> x + y <= INT_MAX) && (x < 0 && y < 0 ==> x + y >= INT_MIN);
ensures \result == x + y;
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