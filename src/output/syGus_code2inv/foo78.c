
/*@
    requires x >= y  && y >= 0;
    */
    
void foo78(int x, int y) {

    int i = 0;
    
    
    
            
        /* >>> LOOP INVARIANT TO FILL <<< */
        
            /*@
            loop invariant 0 <= i <= y;
            */
            while (unknown()) {
      if ( i < y )
      {
      i  = (i + 1);
      }
  
    }
            
    
  /*@ assert (i < y) ==> (i >= 0); */
    
}
