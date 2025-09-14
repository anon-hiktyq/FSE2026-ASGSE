
void foo47(int x, int y) {

    int i = x;
    int j = y;
    
    /* >>> LOOP INVARIANT TO FILL <<< */
        
    /*@
      loop invariant (\at(x,Pre) != 0) ==> (y - x == j - i);
      loop invariant (!(\at(x,Pre) != 0)) ==> ((j == \at(y,Pre))&&(i == \at(x,Pre))&&(y == \at(y,Pre))&&(x == \at(x,Pre)));
      loop invariant j == \at(y,Pre);
      loop invariant i == \at(x,Pre);
      loop assigns x, y;
      loop variant x;
    */
    while (x != 0) {
  
      x  = x - 1;
      y  = y - 1;
  
    }
            
    /*@ assert (y != 0) ==> (i != j); */
  
}
