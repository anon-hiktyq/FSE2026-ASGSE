
void foo84(int y) {

    int x = -50;
  
    
    
            
        /* >>> LOOP INVARIANT TO FILL <<< */
        
            /*@
          loop invariant y >= \at(y, Pre); // Ensures y starts from its initial value and increments
          loop assigns x, y;
            */
            while (x < 0) {
      
      x  = x + y;
      y  = y + 1;
      
  
    }
            
    /*@ assert y > 0; */
  
}
