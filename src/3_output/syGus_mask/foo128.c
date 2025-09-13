
void foo128(int y) {

    int x = 1;
    
    /* >>> LOOP INVARIANT TO FILL <<< */
    
    /*@
      loop invariant (!(1 < \at(y,Pre))) ==> ((x == 1) && (y == \at(y,Pre)));
      loop invariant y == \at(y,Pre);
      loop assigns x;
    */
    while (x < y) {
        x = x + x;
    }
}
