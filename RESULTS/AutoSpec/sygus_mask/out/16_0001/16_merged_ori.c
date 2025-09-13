/*@
requires n > 0;
*/
void foo(int n)
{
    int x = 0;
    int m = 0;

    /*@
    loop invariant x <= n;
    loop invariant m == x ==> \exists integer k; 0 <= k < x && unknown();
    loop invariant m == \max( \{ y | 0 <= y < x \land unknown() \} );
    loop invariant m <= x;
    loop invariant m <= n;
    loop invariant \forall integer k; 0 <= k < x ==> (unknown() ==> m >= k);
    loop invariant \forall integer k; 0 <= k < x ==> (unknown() ==> m == k);
    loop invariant \exists integer k; 0 <= k < x ==> (unknown() ==> m == k);
    loop invariant 0 <= x;
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
