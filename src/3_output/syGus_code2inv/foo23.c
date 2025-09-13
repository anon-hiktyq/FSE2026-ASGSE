
void foo23() {
  
    int i=1;
    int j=20;
   
    
    
            
        /* >>> LOOP INVARIANT TO FILL <<< */
        
            /*@
          loop invariant j == 20 - (i - 1) / 2; 
          loop invariant i == 1 + 2 * (20 - j); 
          loop invariant j + (i - 1) / 2 == 20; // This invariant ensures j reaches 13
          loop invariant j >= 13; // New invariant to ensure j does not drop below 13 until loop ends
          loop assigns i, j;
            */
            while (j >= i) {
      
      i  = i + 2;
      j  = j - 1;
      
  
    }
            
  
    /*@ assert j == 13;*/
  
  }
