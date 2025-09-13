
/*@ 
requires 0 <= k && k <= 1;
*/
void foo006(int k) {
    int i, j;
    i = 1;
    j = 1;


    /*@
    loop invariant k <= 1 && k >= 0;
    loop invariant j <= i;
    loop invariant j <= i + k;
    loop invariant i + k == j + 1;
    loop invariant i + k == 2;
    loop invariant i + k <= 1000002;
    loop invariant i + k <= 1000001;
    loop invariant \forall integer n; 1 <= n <= i ==> 1 <= n + k && n + k <= 2;
    loop invariant \forall integer n; 1 <= n <= i ==> 1 <= i + k && i + k <= 2;
    loop invariant 1 <= j;
    loop invariant 0 <= k;
    loop invariant k <= 1;
    loop invariant i <= 1000000;
    loop invariant i + k <= 2;
    loop invariant 1 <= i;
    loop invariant 1 <= i + k;
    loop invariant 1 <= i + k && i + k <= 2;
    loop invariant 0 <= i;
    loop assigns k;
    loop assigns j;
    loop assigns i;
    */
    while (i < 1000000) {
        i = i + 1;
        j = j + k;
        k = k - 1;
        // @ assert 1 <= i + k && i + k <= 2 && i >= 1;*/
    }
}
