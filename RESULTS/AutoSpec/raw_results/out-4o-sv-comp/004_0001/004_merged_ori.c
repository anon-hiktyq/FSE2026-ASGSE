
void foo004() {
    int i, j;
    i = 1;
    j = 10;
    
    
    /*@
    loop invariant j == 10 - (\floor((i - 1) / 2));
    loop invariant j <= 10;
    loop invariant i <= j + 9;
    loop invariant i <= j + 2;
    loop invariant i <= j + 1;
    loop invariant i <= 2*j + 1;
    loop invariant i <= 19;
    loop invariant i - j == 11 - 2 * (1 + i / 2);
    loop invariant i - 2 <= j;
    loop invariant i - 1 <= j;
    loop invariant i % 2 == 1;
    loop invariant 6 <= j;
    loop invariant 4 <= j;
    loop invariant 1 <= i;
    loop invariant 0 <= j;
    loop invariant 0 <= i;
    loop invariant (j - i) % 3 == 0;
    loop assigns j;
    loop assigns i;
    */
    while (j >= i) {
        i = i + 2;
        j = j - 1;
    }
    
    // @ assert j == 6;
}
