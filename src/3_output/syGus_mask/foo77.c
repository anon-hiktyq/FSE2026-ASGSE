
/*@
    requires x >= y  && y >= 0;
    */
    
void foo77(int x, int y) {

    int i = 0;
    
    /*@
        loop invariant (\at(x, Pre) >= \at(y, Pre) && \at(y, Pre) >= 0) ==> (0 <= i <= y);
        loop invariant (\at(x, Pre) >= \at(y, Pre) && \at(y, Pre) >= 0) ==> (y == \at(y, Pre));
        loop invariant (\at(x, Pre) >= \at(y, Pre) && \at(y, Pre) >= 0) ==> (x == \at(x, Pre));
        loop assigns i;
    */
    while (unknown()) {
        if (i < y) {
            i = (i + 1);
        }
    }
}
