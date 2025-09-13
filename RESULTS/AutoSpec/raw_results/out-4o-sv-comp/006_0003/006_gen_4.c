
/*@ 
requires 0 <= k && k <= 1;
*/
void foo006(int k) {
    int i, j;
    i = 1;
    j = 1;


    /*@
    loop invariant 1 <= i <= 1000000;
    loop invariant 0 <= k <= 1;
    loop invariant 1 <= i + k <= 2;
    loop invariant i + k == 2 || i + k == 1;
    loop assigns i;
    loop assigns j;
    loop assigns k;
    */
    while (i < 1000000) {
        i = i + 1;
        j = j + k;
        k = k - 1;
        // @ assert 1 <= i + k && i + k <= 2 && i >= 1;*/
    }
}
