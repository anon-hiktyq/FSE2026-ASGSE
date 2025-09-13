
/*@
    requires x >= 0 && x <= 2 && y <= 2 && y >= 0;
    */
    
void foo10(int x,int y) {

  
    
            
        /* >>> LOOP INVARIANT TO FILL <<< */
        
            /*@
          loop invariant x >= 0 && y >= 0;
          loop invariant x <= 2 + 2 * ((y - \at(y, Pre)) / 2); // Ensures x does not exceed the maximum possible value
          loop invariant y <= 2 + 2 * ((y - \at(y, Pre)) / 2); // Ensures y does not exceed the maximum possible value
          loop invariant (y == \at(y, Pre) + 2 * ((y - \at(y, Pre)) / 2)) && (x == \at(x, Pre) + 2 * ((y - \at(y, Pre)) / 2));
          loop assigns x, y;
            */
            while (unknown()) {
      
      x  = x + 2;
      y  = y + 2;

    }
            
      /*@ assert (y == 0) ==> (x != 4);  */
  
  }
