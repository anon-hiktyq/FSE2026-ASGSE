
/*@
    requires 0 <= k && k <= 1;
    */
    
void foo006(int k) {
    int i, j;
    i = 1;
    j = 1;

    /*@
        loop invariant k == \at(k, Pre) - (i - 1);
        loop invariant i >= 1;
        loop invariant j == 1 + (i - 1) * \at(k, Pre) - (i - 1) * (i - 2) / 2;
        loop assigns i, j, k;
    */
    while (i < 1000000) {
        i = i + 1;
        j = j + k;
        k = k - 1;
        /*@ assert 1 <= i + k && i + k <= 2 && i >= 1;*/
    }
}
