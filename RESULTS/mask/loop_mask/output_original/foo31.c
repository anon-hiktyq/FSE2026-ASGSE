
void foo31(int y) {

    int x = -5000;

    /*@
        loop invariant y >= \at(y, Pre);
        loop assigns x, y;
        loop variant -x;
    */
    while (x < 0) {
        x = x + y;
        y = y + 1;
    }

    /* mask_1 */
}
