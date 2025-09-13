
void foo51() {
    int x = 1;
    int y = 0;

    /*@
      loop invariant x == 1 + (y * (y - 1)) / 2;
      loop invariant y >= 0 && y <= 1000;
      loop assigns x, y;
      loop variant 1000 - y;
    */
    while (y < 1000) {
        x = x + y;
        y = y + 1;
    }

    /* mask_1 */
}
