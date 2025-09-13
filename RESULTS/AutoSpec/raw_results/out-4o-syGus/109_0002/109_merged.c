/*@
requires c>0;
*/
void foo(int a, int m, int c) {
    int j = 0;
    int k = 0;

    /*@
    loop invariant m >= a || k == 0;
    loop invariant m >= a ==> k <= c;
    loop invariant k < c + 1;
    loop invariant j == 0;
    loop invariant j <= k;
    loop invariant c > 0 ==> a <= m;
    loop invariant a <= m;
    loop invariant a <= m || k == 0;
    loop invariant \forall integer p; 0 <= p < k ==> a <= m;
    loop invariant \forall integer i; 0 <= i < k ==> m >= a;
    loop invariant 0 <= j;
    loop invariant 0 <= c;
    loop invariant 0 < c;
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