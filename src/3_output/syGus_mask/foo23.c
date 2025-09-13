
void foo23() {
  
    int i = 1;
    int j = 20;
   
    /* >>> LOOP INVARIANT TO FILL <<< */
    
    /*@
      loop invariant i % 2 == 1;
      loop invariant j <= 20;
      loop assigns i, j;
    */
    while (j >= i) {
      
      i = i + 2;
      j = j - 1;
      
    }
}
