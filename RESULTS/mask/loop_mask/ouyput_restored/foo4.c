
/*@
    requires x >= 0 && x <= 10 && y <= 10 && y >= 0;
*/
void foo4(int x, int y) {
    /*@
        loop invariant x >= \at(x, Pre) && y >= \at(y, Pre);
        loop invariant (x - \at(x, Pre)) % 10 == 0;
        loop invariant (y - \at(y, Pre)) % 10 == 0;
        loop invariant (x - \at(x, Pre)) == (y - \at(y, Pre));
        loop invariant \at(x, Pre) >= 0 && \at(x, Pre) <= 10;
        loop invariant \at(y, Pre) >= 0 && \at(y, Pre) <= 10;
        loop assigns x, y;
        loop variant 0; // unknown() does not guarantee termination, so variant is set to 0
    */
    while (unknown()) {
        x = x + 10;
        y = y + 10;
    }
    /*@ assert (x ==20) ==>  (y != 0); */
    /* mask_1 */
}
