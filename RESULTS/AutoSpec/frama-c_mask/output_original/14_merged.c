#include <limits.h>


/*@
requires INT_MIN-x <= y <= INT_MAX-x;
requires INT_MIN <= x - y <= INT_MAX;
requires INT_MIN < y <= INT_MAX;
requires INT_MIN < x <= INT_MAX;
requires INT_MIN < x - y <= INT_MAX;
requires INT_MIN - y <= x <= INT_MAX - y;
ensures \result == x-y;
ensures \result == x - y;
assigns \nothing;
*/
int diff (int x, int y) {
    return x-y;
}

void main() {
    int t = diff(10, 5);
   
}