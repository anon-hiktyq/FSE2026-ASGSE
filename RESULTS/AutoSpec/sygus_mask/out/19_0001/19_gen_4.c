/*@
requires n > 0;
*/
void foo(int n)
{
    int x = 0;
    int m = 0;

    /*@
    loop invariant 0 <= x <= n;
    loop invariant m <= n;
    loop invariant m == \max( \{ k | 0 <= k < x \land unknown() \} );
    loop assigns x;
    loop assigns m;
    */
    while (x < n) {
        if (unknown()) {
            m = x;
        }
        x = x + 1;
    }


}
