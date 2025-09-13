
/*@
    requires x >= 0 && x <= 10 && y <= 10 && y >= 0;
*/
void foo8(int x, int y, int z1, int z2, int z3) {
    
    /* >>> LOOP INVARIANT FILLED <<< */
    
    /*@
        loop invariant x >= \at(x,Pre) && x % 10 == \at(x,Pre) % 10;
        loop invariant y >= \at(y,Pre) && y % 10 == \at(y,Pre) % 10;
        loop invariant x - y == \at(x,Pre) - \at(y,Pre);
        loop invariant z3 == \at(z3,Pre);
        loop invariant z2 == \at(z2,Pre);
        loop invariant z1 == \at(z1,Pre);
        loop assigns x, y;
        loop assigns z1, z2, z3; // These variables are unchanged
        loop variant 0; // No guarantee of termination
    */
    while (unknown()) {
        x = x + 10;
        y = y + 10;
    }
    
    /*@ assert (x == 20) ==> (y != 0); */
}
