/*@
requires c>0;
*/
void foo(int a, int m, int c) {
    int j = 0;
    int k = 0;

    /*@
    loop invariant m >= a || m < a;
    loop invariant 0 <= k <= c;
    loop invariant c > 0;
    loop assigns k, m;
    loop invariant k <= c;
    loop invariant j == 0;
    loop invariant 0 <= k;
    loop invariant 0 < c;
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