
void foo32(int y) {

    int x = -50;
  
    
    
            
        /* >>> LOOP INVARIANT TO FILL <<< */
        
            /*@
              loop invariant y == \at(y, LoopEntry) + (y - \at(y, LoopEntry));
              loop invariant x == -50 + (y - \at(y, LoopEntry)) * (\at(y, LoopEntry)) + ((y - \at(y, LoopEntry)) * ((y - \at(y, LoopEntry)) - 1)) / 2;
            */
            while (x < 0) {
      
      x  = x + y;
      y  = y + 1;
      
  
    }
    /*@ assert y > 0; */
            
    /* mask_1 */
  
  }
