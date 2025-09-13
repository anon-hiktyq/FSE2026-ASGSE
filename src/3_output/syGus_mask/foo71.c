
/*@
    requires 0 <= y && y <= 127;
*/
void foo71(int y) {
    int c = 0;
    int z = 36 * y;
    
    /*@
        loop invariant (\at(y, Pre) >= 0 && \at(y, Pre) <= 127) ==> (0 <= c <= 36);
        loop invariant (\at(y, Pre) >= 0 && \at(y, Pre) <= 127) ==> (z == 36 * \at(y, Pre) + c);
        loop invariant (\at(y, Pre) >= 0 && \at(y, Pre) <= 127) ==> (y == \at(y, Pre));
        loop assigns c, z;
    */
    while (unknown()) {
        if (c < 36) {
            z = z + 1;
            c = c + 1;
        }
    }
}
