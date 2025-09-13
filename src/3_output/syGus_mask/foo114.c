
void foo114() {

    int sn = 0;
    int x = 0;
    
        /* >>> LOOP INVARIANT TO FILL <<< */
        
        /*@
          loop invariant sn == x;
          loop invariant x >= 0;
          loop invariant sn >= 0;
          loop assigns x, sn;
        */
        while (unknown()) {
  
      x  = (x + 1);
      sn  = (sn + 1);
      
    }
}
