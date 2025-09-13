
void foo20(int y) {
    int x = 1;

    /*@
      loop invariant ((x == 1) && (y == \at(y,Pre))) || (y == 10 - (x - 1));
      loop invariant x >= 1 && x <= 11;
      loop assigns x, y;
      loop variant 11 - x;
    */
    while (x <= 10) {
        y = 10 - x;
        x = x + 1;
    }

    /* mask_1 */
}
