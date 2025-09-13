
void foo24() {
  
    int i=1;
    int j=10;
   
    
    
            
        /* >>> LOOP INVARIANT TO FILL <<< */
        
            /*@
            loop invariant j == 10 - (i - 1) / 2;      // This captures the relationship between j and i
            loop invariant i == 1 + 2 * (10 - j);       // i is always equal to 1 plus twice the number of decrements of j
            loop invariant j >= 0;                       // j is non-negative
            loop invariant j + 1 >= i;                   // Ensures that j is always at least i - 1
            loop assigns i, j;                           // i and j are assigned within the loop
            */
            while (j >= i) {
      
      i  = i + 2;
      j  = j - 1;
      
  
    }
            
  
    /*@ assert j == 6; */
  
  }
