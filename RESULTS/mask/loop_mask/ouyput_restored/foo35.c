
int foo35(int x) {

    int lock = 1;
    int y = x + 1;

    /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
        loop invariant (\at(x,Pre) != \at(x,Pre) + 1) ==> (((y == \at(x,Pre) + 1)&&(lock == 1)&&(x == \at(x,Pre))) || (x <= y));
        loop invariant (\at(x,Pre) != \at(x,Pre) + 1) ==> (((y == \at(x,Pre) + 1)&&(lock == 1)&&(x == \at(x,Pre))) || (lock == 0 || lock == 1));
        loop invariant (\at(x,Pre) != \at(x,Pre) + 1) ==> (y >= \at(x,Pre) + 1);
        loop invariant (!(\at(x,Pre) != \at(x,Pre) + 1)) ==> ((y == \at(x,Pre) + 1)&&(lock == 1)&&(x == \at(x,Pre)));
        loop assigns x, y, lock;
        loop variant y - x;
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
    /*@ assert lock == 1;*/

    /* mask_1 */
}
