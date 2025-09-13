
/*@
    requires x != y;
    */
    
void foo043(int x, int y) {
  int i=0;
  int t=y;
   
  

  
            
        /* >>> LOOP INVARIANT TO FILL <<< */
        
            /*@
              loop invariant y >= t; // Ensures y is at least t
              loop invariant t == \at(y,Pre);
              loop invariant i >= 0; // Adjusted to reflect non-negativity
              loop invariant x == \at(x,Pre);
              loop assigns y, i;
            */
            while (unknown()){
    if (x > 0)   
      y = y + x;
      i = i + 1;
  }
            
   
  /*@ assert y >= t;*/
 
}
