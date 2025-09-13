/*@
requires a <= m;
requires j < 1;
*/
/* 2. FUNC CONTRACT */
void foo(int a, int j, int m) {
    int k = 0;

    /* 1. LOOP INVARIANT */
    while (k < 1) {
        if(m < a) {
            m = a;
        }
        k = k + 1;
    }

}
