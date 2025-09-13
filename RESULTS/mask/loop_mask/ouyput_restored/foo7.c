
/*@
    requires x >= 0 && x <= 2 && y <= 2 && y >= 0;
    */
void foo7(int x, int y) {

    /*@
        loop invariant x >= 0;
        loop invariant y >= 0;
        loop invariant x - y == \at(x,Pre) - \at(y,Pre);
        loop invariant x % 2 == \at(x,Pre) % 2 && y % 2 == \at(y,Pre) % 2;
        loop assigns x, y;
        loop variant 0; // Since the loop condition is unknown(), the variant is constant.
    */
    while (unknown()) {
        x = x + 2;
        y = y + 2;
    }
    /*@ assert (y == 0) ==> (x != 4);  */

    /* mask_1 */
}
