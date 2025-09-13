
void foo004() {
    int i, j;
    i = 1;
    j = 10;
    
    
    /*@
    loop invariant i >= 1;
    loop invariant j <= 10;
    loop invariant j >= i - 1;
    loop invariant (j - i) % 3 == 0;
    loop assigns i, j;
    */
    while (j >= i) {
        i = i + 2;
        j = j - 1;
    }
    
    // @ assert j == 6;
}
