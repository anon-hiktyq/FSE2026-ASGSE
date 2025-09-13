/*@
requires a <= m;
*/
void foo(int a, int m, int c) {
    int j = 0;
    int k = 0;

    /*@
    loop invariant 0 <= k <= c;
    loop invariant m >= a; 
    loop invariant m >= 0; 
    loop assigns m;
    loop assigns k;
    */
    while (k < c) {
        if(m < a) {
            m = a;
        }
        k = k + 1;
    }

}
