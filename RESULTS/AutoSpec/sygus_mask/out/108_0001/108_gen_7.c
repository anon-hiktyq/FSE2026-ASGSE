/*@
requires a <= m;
*/
void foo(int a, int m, int c) {
    int j = 0;
    int k = 0;

    /*@
    loop invariant 0 <= k <= c;
    loop invariant m >= a;
    loop invariant \forall integer l; 0 <= l < k ==> m >= a;
    loop assigns k;
    loop assigns m;
    */
    while (k < c) {
        if(m < a) {
            m = a;
        }
        k = k + 1;
    }

}
