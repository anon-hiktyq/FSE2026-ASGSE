
/*@
    requires x >= 0 && x <= 10 && y <= 10 && y >= 0;
*/
void foo5(int x, int y) {
  
    /*@
        loop invariant x >= \at(x,Pre) && y >= \at(y,Pre);
        loop invariant x - y == \at(x,Pre) - \at(y,Pre);
        loop invariant x % 10 == \at(x,Pre) % 10 && y % 10 == \at(y,Pre) % 10;
        loop invariant x == \at(x,Pre) + 10 * ((x - \at(x,Pre)) / 10);
        loop invariant y == \at(y,Pre) + 10 * ((y - \at(y,Pre)) / 10);
        loop assigns x, y;
        loop variant 0; // unknown() does not guarantee termination
    */
    while (unknown()) {
        x = x + 10;
        y = y + 10;
    }

    /*@ assert (y == 0) ==> (x != 20); */
}
