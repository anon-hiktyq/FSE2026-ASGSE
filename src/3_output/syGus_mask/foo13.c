
/*@
    requires x >= 0 && x <= 2 && y <= 2 && y >= 0;
    */
void foo13(int x, int y, int z1, int z2, int z3) {

    /*@
        loop invariant (\at(x,Pre) >= 0 && \at(x,Pre) <= 2 && \at(y,Pre) <= 2 && \at(y,Pre) >= 0) ==> (x >= \at(x,Pre));
        loop invariant (\at(x,Pre) >= 0 && \at(x,Pre) <= 2 && \at(y,Pre) <= 2 && \at(y,Pre) >= 0) ==> (y >= \at(y,Pre));
        loop invariant (\at(x,Pre) >= 0 && \at(x,Pre) <= 2 && \at(y,Pre) <= 2 && \at(y,Pre) >= 0) ==> (z3 == \at(z3,Pre));
        loop invariant (\at(x,Pre) >= 0 && \at(x,Pre) <= 2 && \at(y,Pre) <= 2 && \at(y,Pre) >= 0) ==> (z2 == \at(z2,Pre));
        loop invariant (\at(x,Pre) >= 0 && \at(x,Pre) <= 2 && \at(y,Pre) <= 2 && \at(y,Pre) >= 0) ==> (z1 == \at(z1,Pre));
        loop invariant x - y == \at(x,Pre) - \at(y,Pre);
        loop assigns x, y;
    */
    while (unknown()) {
        x = x + 2;
        y = y + 2;
    }
}
