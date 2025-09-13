/*@
requires c>0;
*/
void foo(int a, int m, int c) {
    int j = 0;
    int k = 0;

    /*@
    loop invariant 0 <= j <= k <= c;
    loop invariant m >= a;
    loop invariant k == j;
    loop invariant \forall integer i; 0 <= i < k ==> m >= a;
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