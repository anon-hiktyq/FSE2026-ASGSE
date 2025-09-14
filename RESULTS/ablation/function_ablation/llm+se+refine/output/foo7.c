
/*@
    requires x >= 0 && x <= 2 && y <= 2 && y >= 0;
    */
    
void foo7(int x,int y) {

        /*@
            loop invariant x >= 0 && y >= 0;
            loop invariant x - y == \at(x, Pre) - \at(y, Pre);
            loop invariant x % 2 == \at(x, Pre) % 2;
            loop invariant y % 2 == \at(y, Pre) % 2;
            loop invariant x == \at(x, Pre) + 2 * ((x - \at(x, Pre)) / 2);
            loop invariant y == \at(y, Pre) + 2 * ((y - \at(y, Pre)) / 2);
            loop assigns x, y;
            loop variant 0; // Non-deterministic termination
        */
        while (unknown()) {
            x = x + 2;
            y = y + 2;
        }
            
      /*@ assert (y == 0) ==> (x != 4);  */
}
