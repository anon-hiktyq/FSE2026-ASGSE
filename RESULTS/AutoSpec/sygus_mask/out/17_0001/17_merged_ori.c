/*@
requires n > 1;
*/
void foo(int n)
{
    int x = 1;
    int m = 1;

    /*@
    loop invariant x <= n;
    loop invariant x < n;
    loop invariant m == x || m < x;
    loop invariant m == \max(1, x) if unknown() is true;
    loop invariant m == \max(1, \{ j | 1 <= j < x \land unknown() \});
    loop invariant m == \max(1, \max_{0 <= k < x}(unknown() ? k : 1));
    loop invariant m == (unknown() ? x - 1 : m);;
    loop invariant m == (unknown() ? x - 1 : m);
    loop invariant m <= x;
    loop invariant m <= n;
    loop invariant 1 <= x;
    loop invariant 1 <= m;
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
