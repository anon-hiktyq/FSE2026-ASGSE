
void foo004() {
    int i, j;
    i = 1;
    j = 10;
    
    
    /*@
    loop invariant i <= j + 1;
    loop invariant i % 2 == 1;
    loop invariant j >= 0;
    loop invariant j == 10 - (\floor((i - 1) / 2));
    loop assigns i, j;
    */
    while (j >= i) {
        i = i + 2;
        j = j - 1;
    }
    
    // @ assert j == 6;
}
