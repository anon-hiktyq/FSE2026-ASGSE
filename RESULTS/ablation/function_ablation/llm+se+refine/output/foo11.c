
/*@
    requires x >= 0 && x <= 2 && y <= 2 && y >= 0;
    ensures (y == 0) ==> (x != 4);
*/
void foo11(int x, int y, int z1, int z2, int z3) {

    /*@
        loop invariant x - y == \at(x, Pre) - \at(y, Pre);
        loop invariant x >= \at(x, Pre);
        loop invariant y >= \at(y, Pre);
        loop invariant z3 == \at(z3, Pre);
        loop invariant z2 == \at(z2, Pre);
        loop invariant z1 == \at(z1, Pre);
        loop assigns x, y;
        loop variant 0; // Since the number of iterations is unknown, we use a constant variant
    */
    while (unknown()) {
        x = x + 2;
        y = y + 2;
    }

    /*@ assert (y == 0) ==> (x != 4); */
}
