/*@
requires a <= m;
requires j < 1;
*/
void foo(int a, int j, int m) {
    int k = 0;

    /*@
    loop invariant 0 <= k <= 1;
    loop invariant m >= a;
    loop invariant m >= \old(m);
    loop assigns k, m;
    */
    while (k < 1) {
        if(m < a) {
            m = a;
        }
        k = k + 1;
    }
    //post-condition
    // @ assert a >= m;
}
