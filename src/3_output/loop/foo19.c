
void foo19(int y) {
    int x = 1;
    
    /* >>> LOOP INVARIANT TO FILL <<< */
        
    /*@
      loop invariant y >= 0 || (x == 1 && y == \at(y,Pre));
      loop invariant x >= 1 && x <= 11;
    */
    while (x <= 10) {
        y = 10 - x;
        x = x + 1;
    }

    /*@ assert (y >= 0); */
}
