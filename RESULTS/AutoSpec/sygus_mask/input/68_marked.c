/*@
requires n > 0;
*/
/* 2. FUNC CONTRACT */
void foo(int n) {
    int y = 0;
    int x = 1;

    /* 1. LOOP INVARIANT */
    while (x <= n) {
        y = n - x;
        x = x +1;
    }


}
