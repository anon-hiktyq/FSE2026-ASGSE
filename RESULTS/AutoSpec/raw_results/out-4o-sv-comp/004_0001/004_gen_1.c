
void foo004() {
    int i, j;
    i = 1;
    j = 10;
    
    
    /*@
    loop invariant i <= j + 2;
    loop invariant 1 <= i <= 2*j + 1;
    loop invariant j >= 0;
    loop assigns i;
    loop assigns j;
    */
    while (j >= i) {
        i = i + 2;
        j = j - 1;
    }
    
    // @ assert j == 6;
}
