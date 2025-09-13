
/*@ 
requires 0 <= k && k <= 1;
*/
void foo006(int k) {
    int i, j;
    i = 1;
    j = 1;


    /*@
    loop invariant 1 <= i;
    loop invariant k <= 1;
    loop invariant i + k <= i + 1;
    loop invariant i + k >= i;
    loop invariant \forall integer m; 1 <= m <= i ==> 1 <= m + k && m + k <= m + 1;
    loop invariant j == i - k;
    loop assigns j;
    loop invariant k <= 1;
    loop invariant i <= 1000000;
    loop invariant i + k <= 2;
    loop invariant 1 <= i;
    loop invariant 1 <= i + k;
    loop invariant 1 <= i + k && i + k <= 2;
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
