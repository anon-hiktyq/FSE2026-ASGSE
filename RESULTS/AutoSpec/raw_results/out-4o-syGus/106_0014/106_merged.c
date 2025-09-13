/*@
requires a <= m;
requires j < 1;
*/
void foo(int a, int j, int m) {
    int k = 0;

    /*@
    loop invariant m >= a || k >= 1;
    loop invariant m >= a || k >= 1 && m >= a;
    loop invariant k == 1 || m >= a;
    loop invariant k == 1 ==> m == a;
    loop invariant k == 0 || m == a;
    loop invariant k == 0 ==> m < a;
    loop invariant k == 0 ==> m < 2*a;
    loop invariant \forall integer x; k == 1 ==> m == a;
    loop invariant \forall integer x; 0 <= x <= k ==> m >= a;
    loop invariant 1 - k;
    loop invariant m >= a || (k >= 1 && m >= a);
    loop invariant k >= 0 && k <= 1;
    loop invariant k == 1 || k == 0;
    loop invariant k == 1 ==> m >= a;
    loop invariant k == 0 || m >= a;
    loop invariant k == 0 || k == 1;
    loop invariant k <= 1;
    loop invariant k < 2;
    loop invariant j < 1;
    loop invariant a <= m;
    loop invariant \forall integer x; 0 <= x < k ==> m >= a;
    loop invariant \forall integer n; 0 <= n < k ==> m >= a;
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
