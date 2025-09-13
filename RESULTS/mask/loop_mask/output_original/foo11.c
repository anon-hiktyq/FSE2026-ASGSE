
/*@
    requires x >= 0 && x <= 2 && y <= 2 && y >= 0;
*/
void foo11(int x, int y, int z1, int z2, int z3) {

    /*@
        loop invariant x == \at(x, Pre) + 2 * (\at(x, Here) - \at(x, Pre)) / 2;
        loop invariant y == \at(y, Pre) + 2 * (\at(y, Here) - \at(y, Pre)) / 2;
        loop invariant z3 == \at(z3, Pre);
        loop invariant z2 == \at(z2, Pre);
        loop invariant z1 == \at(z1, Pre);
        loop assigns x, y;
        loop variant 0; // unknown() does not guarantee termination, so no decreasing variant can be defined
    */
    while (unknown()) {
        x = x + 2;
        y = y + 2;
    }

    /* mask_1 */
}
