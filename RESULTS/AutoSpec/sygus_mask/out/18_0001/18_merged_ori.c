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
    loop invariant m == \max(1, x);
    loop invariant m == \max(1, \{ x | 1 <= x < x \land unknown() \});
    loop invariant m == \max(1, \{ k | 1 <= k < x \land unknown() \});
    loop invariant m <= x;
    loop invariant \forall integer k; 1 <= k < x ==> m >= k;
    loop invariant \forall integer k; 1 <= k < x ==> m <= k;
    loop invariant 1 <= x;
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
