
void foo14() {
    int i = 1;
    int j = 10;
    
    /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
      loop invariant j + i == 11 + (i - 1) / 2;
      loop invariant i % 2 == 1;
      loop invariant j >= 6;
      loop assigns i, j;
    */
    while (j >= i) {
        i = i + 2;
        j = j - 1;
    }
    
    /*@ assert j == 6; */
}
