
void foo33(int y, int z1, int z2, int z3) {

    int x = -15000;

    /*@
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

    /* mask_1 */
}
