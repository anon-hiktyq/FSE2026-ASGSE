/*@
requires n > 1;
*/
/* 2. FUNC CONTRACT */
void foo(int n)
{
    int x = 1;
    int m = 1;

    /* 1. LOOP INVARIANT */
    while (x < n) {
        if (unknown()) {
            m = x;
        }
        x = x + 1;
    }


}
