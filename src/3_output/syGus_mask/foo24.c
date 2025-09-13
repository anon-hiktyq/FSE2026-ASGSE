
void foo24() {
  
    int i = 1;
    int j = 10;
   
    /* >>> LOOP INVARIANT TO FILL <<< */
    
    /*@
      loop invariant i == 1 + 2 * ((10 - j) / 1);
      loop invariant j == 10 - ((i - 1) / 2);
      loop assigns i, j;
    */
    while (j >= i) {
      
      i = i + 2;
      j = j - 1;
      
    }
  
}
