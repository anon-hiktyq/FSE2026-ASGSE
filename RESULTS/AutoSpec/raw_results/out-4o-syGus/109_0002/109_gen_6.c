/*@
requires c>0;
*/
void foo(int a, int m, int c) {
    int j = 0;
    int k = 0;

    /*@
    loop invariant a <= m || k == 0;
    loop invariant k <= c;
    loop invariant c > 0 ==> a <= m;
    loop invariant \forall integer p; 0 <= p < k ==> a <= m;
    loop invariant 0 <= k;
    loop invariant k >= j;
    loop invariant k <= c;
    loop invariant 0 <= k;
    loop assigns m;
    loop assigns k;
    */
    while ( k < c) {
        if(m < a) {
            m = a;
        }
        k = k + 1;
    }

    //post-condition
    if(c > 0) {
        // @ assert a <=  m;
    }
}