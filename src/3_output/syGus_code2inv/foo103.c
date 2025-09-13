
void foo103() {

    int x = 0 ;
    
    /* >>> LOOP INVARIANT TO FILL <<< */
    
    /*@
      loop invariant x >= 0 && x <= 100;
      loop assigns x;
    */
    while (x < 100) {
        x  = (x + 1);
    }
    
   /*@ assert x == 100 ;*/
}
