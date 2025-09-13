/*@
requires n > 1;
*/
void foo(int n)
{
    int x = 1;
    int m = 1;

    /*@
    loop invariant 1 <= x < n;
    loop invariant m == \max(1, \{ k | 1 <= k < x \land unknown() \});
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
