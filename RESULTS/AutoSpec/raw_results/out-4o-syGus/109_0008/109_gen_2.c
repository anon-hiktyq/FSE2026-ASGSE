/*@
requires c>0;
*/
void foo(int a, int m, int c) {
    int j = 0;
    int k = 0;

    /*@
    loop invariant j == 0;
    loop invariant k >= 0;
    loop invariant k <= c;
    loop invariant c > 0 ==> a <= m;
    loop invariant c > 0 ==> 1 <= k <= c;
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