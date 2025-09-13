
int foo87(int y) {

    int lock = 1;
    int x = y;

    /*@
      loop invariant (\at(y,Pre) != \at(y,Pre)) ==> (y >= \at(y,Pre));
      loop invariant (\at(y,Pre) != \at(y,Pre)) ==> (((x == \at(y,Pre))&&(lock == 1)&&(y == \at(y,Pre))) || ((lock == 0) && (x == y) && (y > \at(y,Pre))));
      loop invariant (\at(y,Pre) != \at(y,Pre)) ==> (((x == \at(y,Pre))&&(lock == 1)&&(y == \at(y,Pre))) || ((x == y) && (lock == 0) && (y > \at(y,Pre))));
      loop invariant (!(\at(y,Pre) != \at(y,Pre))) ==> ((x == \at(y,Pre))&&(lock == 1)&&(y == \at(y,Pre)));
      loop assigns x, y, lock;
    */
    while (x != y) {
        if (unknown()) {
            lock = 1;
            x = y;
        } else {
            lock = 0;
            x = y;
            y = y + 1;
        }
    }
}
