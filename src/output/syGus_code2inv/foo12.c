
/*@
    requires x >= 0 && x <= 10 && y <= 10 && y >= 0;
    */
    
void foo12(int x, int y,int z1,int z2,int z3) {
  
        /* >>> LOOP INVARIANT TO FILL <<< */
        
            /*@
          loop invariant (x - y) == (\at(x, Pre) - \at(y, Pre));
          loop invariant z3 == \at(z3,Pre);
          loop invariant z2 == \at(z2,Pre);
          loop invariant z1 == \at(z1,Pre);
          loop assigns x, y;
            */
            while (unknown()) {
      
        x = x + 10;
        y = y + 10;
      
    }
            

    /*@ assert (y == 0) ==>  (x != 20); */
  
   
  }
