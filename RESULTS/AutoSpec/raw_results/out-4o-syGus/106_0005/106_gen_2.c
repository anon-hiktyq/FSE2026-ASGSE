/*@
requires a <= m;
requires j < 1;
*/
void foo(int a, int j, int m) {
    int k = 0;

    /*@
    loop invariant k <= 1;  
    loop invariant a <= m;  
    loop invariant 0 <= k;  
    loop invariant m >= a;  
    loop invariant k == 0 || k == 1;  
    loop invariant \forall integer n; 0 <= n < k ==> m >= a;
    loop invariant k <= 1;
    loop invariant a <= m;
    loop invariant 0 <= k;
    loop assigns m;
    loop assigns k;
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
