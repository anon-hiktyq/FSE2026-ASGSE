
/*@
    requires x >= 0 && x <= 2 && y <= 2 && y >= 0;
    */
    
void foo9(int x, int y) {

  
    
            
        /*@
            loop invariant (x - \at(x,Pre)) == (y - \at(y,Pre));
            loop invariant (y - \at(y,Pre)) == (x - \at(x,Pre));
            loop assigns x, y;
            loop variant \at(x, Pre) + \at(y, Pre);
        */
            while (unknown()) {
      
      x  = x + 2;
      y  = y + 2;

    }
            
  
    /*@ assert (x == 4) ==> (y != 0);  */
  
    
  
}
