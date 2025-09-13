/*@
requires n > 0;
*/
/* 2. FUNC CONTRACT */
void foo(int n) {
    int x = 1;
    int y = 0;

    /* 1. LOOP INVARIANT */
    while (x <= n) {
        y = n - x;
        x = x +1;
    }

}
