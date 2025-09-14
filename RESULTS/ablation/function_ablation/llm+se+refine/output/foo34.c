
void foo34(int y, int z1, int z2, int z3) {

    int x = -50;
    
    /* >>> LOOP INVARIANT TO FILL <<< */
    
    /*@
      loop invariant y > 0 || x < 0;
      loop invariant y >= \at(y, Pre);
      loop invariant z3 == \at(z3, Pre);
      loop invariant z2 == \at(z2, Pre);
      loop invariant z1 == \at(z1, Pre);
      loop assigns x, y;
      loop variant -x;
    */
    while (x < 0) {
        x = x + y;
        y = y + 1;
    }
    
    /*@ assert y > 0; */
}
