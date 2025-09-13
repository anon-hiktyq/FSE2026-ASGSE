
/*@
    requires x >= 0 && x <= 10 && y <= 10 && y >= 0;
    */
    
void foo8(int x, int y) {
  
    /*@
        loop invariant 0 <= x <= 10 + 10 * ((x - \at(x, Pre)) / 10); // Express x in terms of its initial value
        loop invariant 0 <= y <= 10 + 10 * ((y - \at(y, Pre)) / 10); // Express y in terms of its initial value
        loop invariant (y == \at(y, Pre) + 10 * ((x - \at(x, Pre)) / 10)); // Relate y to its initial value
        loop invariant (x == \at(x, Pre) + 10 * ((x - \at(x, Pre)) / 10)); // Relate x to its initial value
        loop assigns x, y;
    */
    while (unknown()) {
        x = x + 10;
        y = y + 10;
    }
    
    /*@ assert (y == 0) ==> (x != 20); */
    
}
