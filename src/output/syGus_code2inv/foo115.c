
void foo115() {

    int sn = 0;
    int x = 0;
    
    /* >>> LOOP INVARIANT TO FILL <<< */
    
    /*@
      loop invariant sn == x;
      loop invariant sn >= 0;
      loop invariant x >= 0;
      loop assigns x, sn;
    */
    while (unknown()) {
  
      x  = (x + 1);
      sn  = (sn + 1);
      
    }
            
    /*@ assert (sn != -1) ==> (sn == x);*/
}
