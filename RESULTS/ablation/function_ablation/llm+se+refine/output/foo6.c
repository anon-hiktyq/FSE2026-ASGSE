
/*@
    requires x >= 0 && x <= 2 && y <= 2 && y >= 0;
    */
void foo6(int x,int y) {
    /*@
      loop invariant x >= \at(x,Pre);
      loop invariant y >= \at(y,Pre);
      loop invariant x - y == \at(x,Pre) - \at(y,Pre);
      loop invariant (x % 2 == \at(x,Pre) % 2) && (y % 2 == \at(y,Pre) % 2);
      loop assigns x, y;
    */
    while (unknown()) {
        x = x + 2;
        y = y + 2;
    }
    /*@ assert (x == 4) ==> (y != 0); */
}
