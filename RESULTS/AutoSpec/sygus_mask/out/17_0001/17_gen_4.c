/*@
requires n > 1;
*/
void foo(int n)
{
    int x = 1;
    int m = 1;

    /*@
    loop invariant 1 <= x < n;
    loop invariant m == \max(1, \max_{0 <= k < x}(unknown() ? k : 1));
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
