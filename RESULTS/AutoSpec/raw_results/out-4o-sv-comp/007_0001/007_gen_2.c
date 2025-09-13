/*@
requires 0 < n;
*/
void foo007(int n) {
    int k = 0;
    int i = 0;


    /*@
    loop invariant 0 <= i <= n;
    loop invariant k == i;
    loop assigns i, k;
    
    loop invariant 0 <= j <= n;
    loop invariant k == j;
    loop assigns j, k;
    */
    while (i < n) {
        i++;
        k++;
    }
    int j = n;


    while (j > 0) {
        j--;
        k--;
        // @ assert k >= 0;
    }


}
