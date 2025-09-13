
void foo25() {
    int x = 10000;

    /*@
      loop invariant x >= 0;
      loop invariant x <= 10000;
      loop invariant x == \at(x, Pre) - (10000 - \at(x, Pre));
      loop assigns x;
    */
    while (x > 0) {
        x = x - 1;
    }
}
