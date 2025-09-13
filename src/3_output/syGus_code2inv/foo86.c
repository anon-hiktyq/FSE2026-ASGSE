
void foo86(int y,int z1,int z2,int z3) {

    int x = -50;
  
    
    
            
        /* >>> LOOP INVARIANT TO FILL <<< */
        
            /*@
            loop invariant y >= \at(y, Pre);
            loop invariant y > 0 || x < 0; // Ensure y will eventually become positive
            loop assigns x, y;
            loop variant x + 50;
            */
            while (x < 0) {
      
      x  = x + y;
      y  = y + 1;
      
  
    }
            
    /*@ assert y > 0; */
  
  }
