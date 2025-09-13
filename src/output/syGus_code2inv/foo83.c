
void foo83(int y) {

    int x = -5000;
  
    
    
            
        /* >>> LOOP INVARIANT TO FILL <<< */
        
            /*@
            loop invariant x + 5000 + (y - \at(y, Pre)) * (n) < 0;
            loop invariant y == \at(y, Pre) + n;
            loop invariant x == -5000 + n * \at(y, Pre) + (n * (n - 1) / 2);
            loop assigns x, y;
            */
            while (x < 0) {
      
      x  = x + y;
      y  = y + 1;
      
  
    }
            
    /*@ assert y > 0; */
  
  }
