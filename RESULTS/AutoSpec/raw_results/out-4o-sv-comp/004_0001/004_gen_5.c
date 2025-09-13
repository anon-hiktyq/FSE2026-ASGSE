
void foo004() {
    int i, j;
    i = 1;
    j = 10;
    
    
    /*@
    loop invariant 1 <= i <= j + 2;
    loop invariant j >= i - 2;
    loop invariant j >= 0;
    loop invariant i >= 0;
    loop assigns i, j;
    */
    while (j >= i) {
        i = i + 2;
        j = j - 1;
    }
    
    // @ assert j == 6;
}
