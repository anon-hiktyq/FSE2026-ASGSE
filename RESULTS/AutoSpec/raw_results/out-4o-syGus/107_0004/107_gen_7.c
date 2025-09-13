/*@
requires a <= m;
*/
void foo(int a, int m) {
    int j = 0;
    int k = 0;

    /*@
    loop invariant k >= 0;
    loop invariant k <= 1;
    loop invariant m >= a;
    loop invariant j == 0;
    loop assigns k;
    loop assigns m;
    */
    while ( k < 1) {
        if(m < a) {
            m = a;
        }
        k = k + 1;
    }

    //post-condition
    // @ assert a <= m;
}
