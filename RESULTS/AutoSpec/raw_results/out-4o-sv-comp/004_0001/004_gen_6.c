
void foo004() {
    int i, j;
    i = 1;
    j = 10;
    
    
    /*@
    loop invariant i <= j + 2;
    loop invariant i >= 1;
    loop invariant j <= 10;
    loop invariant j >= 6;
    loop assigns i;
    loop assigns j;
    */
    while (j >= i) {
        i = i + 2;
        j = j - 1;
    }
    
    // @ assert j == 6;
}
