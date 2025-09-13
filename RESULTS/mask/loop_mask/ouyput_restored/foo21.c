
void foo21(int y) {
    int x = 1;

    /*@
        loop invariant ((x == 1 && y == \at(y, Pre)) || (y == 100 - (x - 1)));
        loop invariant x >= 1 && x <= 101;
        loop variant 101 - x;
    */
    while (x <= 100) {
        y = 100 - x;
        x = x + 1;
    }
    /*@ assert (y >= 0); */

    /* mask_1 */
}
