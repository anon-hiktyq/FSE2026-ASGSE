
void foo004() {
    int i, j;
    i = 1;
    j = 10;
    
    /*@
      loop invariant 0 <= j <= 10;
      loop invariant i == 1 + 2 * (10 - j);
      loop invariant j == 10 - (i - 1) / 2; // Existing invariant
      loop invariant j == 6 + (10 - i) / 2; // New invariant to ensure j will be 6 at termination
      loop assigns i, j;
    */
    while (j >= i) {
        i = i + 2;
        j = j - 1;
    }
    
    /*@ assert j == 6; */
    return;
}
