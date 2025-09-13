/*@
requires n > 0;
*/
/* 2. FUNC CONTRACT */
void foo(int n)
{
    int x = 0;
    int m = 0;

    /* 1. LOOP INVARIANT */
    while (x < n) {
        if (unknown()) {
            m = x;
        }
        x = x + 1;
    }


}
