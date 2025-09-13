
/*@
    requires x >= 0 && x <= 2 && y <= 2 && y >= 0;
    ensures x >= \at(x, Pre) && y >= \at(y, Pre) && (x - y == \at(x, Pre) - \at(y, Pre));
*/
void foo10(int x, int y, int z1, int z2, int z3) {

    /*@
        loop invariant x >= \at(x, Pre) && x == \at(x, Pre) + 2 * ((x - \at(x, Pre)) / 2);
        loop invariant y >= \at(y, Pre) && y == \at(y, Pre) + 2 * ((y - \at(y, Pre)) / 2);
        loop invariant x - y == \at(x, Pre) - \at(y, Pre);
        loop invariant z3 == \at(z3, Pre);
        loop invariant z2 == \at(z2, Pre);
        loop invariant z1 == \at(z1, Pre);
        loop assigns x, y;
        loop variant 0; // Unknown loop condition, no decreasing variant can be defined
    */
    while (unknown()) {
        x = x + 2;
        y = y + 2;
    }

    /* mask_1 */
}
