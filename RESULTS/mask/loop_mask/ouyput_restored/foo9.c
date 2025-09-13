
/*@
    requires x >= 0 && x <= 10 && y <= 10 && y >= 0;
*/
void foo9(int x, int y, int z1, int z2, int z3) {
  
    /*@
        loop invariant x >= 0 && x == \at(x,Pre) + 10 * (x - \at(x,Pre)) / 10;
        loop invariant y >= 0 && y == \at(y,Pre) + 10 * (y - \at(y,Pre)) / 10;
        loop invariant z3 == \at(z3,Pre);
        loop invariant z2 == \at(z2,Pre);
        loop invariant z1 == \at(z1,Pre);
        loop assigns x, y;
        loop variant 0; // Since `unknown()` can loop indefinitely, no decreasing variant is defined.
    */
    while (unknown()) {
        x = x + 10;
        y = y + 10;
    }
    /*@ assert (y == 0) ==>  (x != 20); */

    /* mask_1 */
}
