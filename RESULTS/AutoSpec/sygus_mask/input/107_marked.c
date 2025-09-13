/*@
requires a <= m;
*/
/* 2. FUNC CONTRACT */
void foo(int a, int m) {
    int j = 0;
    int k = 0;

    /* 1. LOOP INVARIANT */
    while ( k < 1) {
        if(m < a) {
            m = a;
        }
        k = k + 1;
    }


}
