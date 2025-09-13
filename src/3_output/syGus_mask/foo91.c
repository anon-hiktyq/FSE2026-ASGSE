
void foo91() {

    int x = 0;
    int y = 0;

    /* >>> LOOP INVARIANT TO FILL <<< */
    
    /*@
      loop invariant y == 0;
      loop invariant x == 0;
      loop assigns y;
    */
    while(y >= 0) {
        y = y + x;
    }
}
