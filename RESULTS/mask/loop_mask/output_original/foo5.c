
/*@
    requires x >= 0 && x <= 10 && y <= 10 && y >= 0;
*/
void foo5(int x, int y) {
  
    /*@
        loop invariant x >= \at(x,Pre);
        loop invariant y >= \at(y,Pre);
        loop invariant x - \at(x,Pre) == y - \at(y,Pre);
        loop assigns x, y;
        loop variant 0; // Unknown termination condition
    */
    while (unknown()) {
        x = x + 10;
        y = y + 10;
    }

    /* mask_1 */
}
