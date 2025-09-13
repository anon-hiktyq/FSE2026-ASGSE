/*@
requires n > 1;
*/
void foo(int n)
{
    int x = 1;
    int m = 1;

    /*@
    loop invariant 1 <= x < n;
    loop invariant m <= x;
    loop invariant \forall integer k; 1 <= k < x ==> m <= k;
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
