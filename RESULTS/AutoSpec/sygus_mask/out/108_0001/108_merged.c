/*@
requires a <= m;
*/
void foo(int a, int m, int c) {
    int j = 0;
    int k = 0;

    /*@
    loop invariant m >= a || m >= a;
    loop invariant a <= m;
    loop invariant \forall integer p; 0 <= p < k ==> m >= a;
    loop invariant \forall integer l; 0 <= l < k ==> m >= a;
    loop invariant 0 <= k;
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
