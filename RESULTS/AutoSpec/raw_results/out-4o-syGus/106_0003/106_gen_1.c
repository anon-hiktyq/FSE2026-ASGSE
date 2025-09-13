/*@
requires a <= m;
requires j < 1;
*/
void foo(int a, int j, int m) {
    int k = 0;

    /*@
    loop invariant 0 <= k <= 1;
    loop invariant k == 0 || k == 1;
    loop invariant a <= m;
    loop invariant j < 1;
    loop invariant \forall integer i; 0 <= i < k ==> m >= a;
    loop invariant m >= a && 0 <= k && k <= 1;
    loop invariant k == 0 || k == 1;
    loop invariant k <= 1;
    loop invariant k <= 1 ==> m >= a;
    loop invariant k <= 1 && k >= 0;
    loop invariant j < 1;
    loop invariant a <= m;
    loop invariant a <= m && k <= 1;
    loop invariant a <= k + m;
    loop invariant \forall integer x; 0 <= x < k ==> m >= a;
    loop invariant \forall integer i; 0 <= i < k ==> m >= a;
    loop invariant 0 <= k;
    loop invariant 0 <= k && k <= 1;
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
