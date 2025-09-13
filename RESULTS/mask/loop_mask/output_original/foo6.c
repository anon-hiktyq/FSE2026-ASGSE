
/*@
    requires x >= 0 && x <= 10 && y <= 10 && y >= 0;
    */
void foo6(int x, int y) {
    /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
      loop invariant x >= 0;
      loop invariant y >= 0;
      loop invariant x - y == \at(x,Pre) - \at(y,Pre);
      loop assigns x, y;
      loop variant 0; // Since the termination condition is unknown, we use a constant variant
    */
    while (unknown()) {
        x = x + 10;
        y = y + 10;
    }

    /* mask_1 */
}
