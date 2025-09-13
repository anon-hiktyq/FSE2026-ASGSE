#include <limits.h>


/*@
requires INT_MIN < x <= INT_MAX;
requires INT_MIN < y <= INT_MAX;
assigns \nothing;
ensures \result == x - y;
*/
int diff (int x, int y) {
    return x-y;
}

void main() {
    int t = diff(10, 5);
   
}