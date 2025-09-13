
void foo85(int y,int z1,int z2,int z3) {

    int x = -15000;
  
    
    
            
        /* >>> LOOP INVARIANT TO FILL <<< */
        
            /*@
            loop invariant y >= \at(y,Pre); // Weakened invariant for y
            loop invariant y > 0 || (x + 15000 <= 0); // Adjusted invariant to ensure validity under initial conditions
            loop invariant z3 == \at(z3,Pre);
            loop invariant z2 == \at(z2,Pre);
            loop invariant z1 == \at(z1,Pre);
            loop assigns x, y;
            */
            while (x < 0) {
      
      x  = x + y;
      y  = y + 1;
      
  
    }
            
    /*@ assert y > 0; */
  
  }
