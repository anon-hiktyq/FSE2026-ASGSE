/*@
requires c>0;
*/
void foo(int a, int m, int c) {
    int j = 0;
    int k = 0;

    /*@
    loop invariant m >= a || m == \old(m);
    loop invariant m >= a || m < a;
    loop invariant m >= a || m < a + k;
    loop invariant m >= a || k == 0;
    loop invariant k == c ==> m >= a;
    loop invariant k == 0 ==> m < a || m >= a;
    loop invariant i <= c;
    loop invariant a <= m;
    loop invariant \forall integer x; 0 <= x < k ==> m >= a;
    loop invariant \forall integer i; 0 <= i < k ==> m >= a;
    loop invariant \exists integer x; x == k && k <= c;
    loop invariant \exists integer i; 0 < i;
    loop invariant (k == c) ==> (m >= a);
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