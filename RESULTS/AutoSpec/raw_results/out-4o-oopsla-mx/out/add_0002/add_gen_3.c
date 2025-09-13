#include <limits.h>

/*@
requires (x > 0 && y > 0 ==> x + y > x && x + y > y) && (x < 0 && y < 0 ==> x + y < x && x + y < y);
assigns \nothing;
ensures \result == x + y;
*/
int add(int x, int y) {
    return x+y;
}

void foo() {
    int a = add(1, 43);
    // @ assert a == 44;
    int b = add(INT_MAX, INT_MAX);
}