
void foo84(int y) {

    int x = -50;
  
    /* >>> LOOP INVARIANT TO FILL <<< */
    
    /*@
      loop invariant y >= \at(y, Pre);
      loop assigns x, y;
    */
    while (x < 0) {
        x = x + y;
        y = y + 1;
    }
}
