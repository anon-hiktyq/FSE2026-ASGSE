
void foo14() {
  
    int i = 1;
    int j = 10;
   
    /*@
      loop invariant i == 2 * (10 - j) + 1;
      loop invariant j == 10 - (i - 1) / 2;
      loop invariant j >= 0;
      loop invariant i >= 1;
      loop variant j - i;
    */
    while (j >= i) {
        i = i + 2;
        j = j - 1;
    }
  
    /* mask_1 */
}
