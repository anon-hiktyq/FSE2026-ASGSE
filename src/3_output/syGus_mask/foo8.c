
/*@
    requires x >= 0 && x <= 10 && y <= 10 && y >= 0;
*/
void foo8(int x, int y) {
    /*@
        loop invariant (\at(x, Pre) >= 0 && \at(x, Pre) <= 10 && \at(y, Pre) <= 10 && \at(y, Pre) >= 0) ==> (x - y == \at(x, Pre) - \at(y, Pre));
        loop invariant (\at(x, Pre) >= 0 && \at(x, Pre) <= 10 && \at(y, Pre) <= 10 && \at(y, Pre) >= 0) ==> (x >= \at(x, Pre));
        loop invariant (\at(x, Pre) >= 0 && \at(x, Pre) <= 10 && \at(y, Pre) <= 10 && \at(y, Pre) >= 0) ==> (y >= \at(y, Pre));
        loop assigns x, y;
    */
    while (unknown()) {
        x = x + 10;
        y = y + 10;
    }
}
