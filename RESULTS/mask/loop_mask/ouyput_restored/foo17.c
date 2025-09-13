
/*@
    requires n > 0;
*/
void foo17(int n) {

    int c = 0;

    /*@
        loop invariant ((c == 0 && n == \at(n, Pre)) || (c >= 1 && c <= n));
        loop invariant n == \at(n, Pre);
        loop assigns c;
        loop variant 0; // Since the number of iterations is unknown, we assume it does not decrease
    */
    while (unknown()) {
        if (unknown()) {
            if (c > n) {
                c = c + 1;
            }
        } else {
            if (c == n) {
                c = 1;
            }
        }
    }
    /*@ assert (c != n) ==> (c >= 0); */

    /* mask_1 */
}
