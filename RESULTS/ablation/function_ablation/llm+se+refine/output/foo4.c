
/*@
    requires x >= 0 && x <= 10 && y <= 10 && y >= 0;
    */
void foo4(int x, int y) {
    /*@
        loop invariant x >= 0 && y >= 0;
        loop invariant x - y == \at(x,Pre) - \at(y,Pre);
        loop assigns x, y;
        loop variant x + y;
    */
    while (unknown()) {
        x = x + 10;
        y = y + 10;
    }
    /*@ assert (x == 20) ==> (y != 0); */
}
