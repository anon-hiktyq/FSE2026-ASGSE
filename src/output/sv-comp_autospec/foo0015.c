
/*@
    requires y <= 1000000;
    requires \at(y, Pre) > 0 && \at(y, Pre) <= 1000000 && (y == \at(y, Pre)) && (x == \at(x, Pre));
    ensures y <= 0 || (y > 0 && x >= 100);
*/
void foo0015(int x, int y) {

    if (y > 0) {
        
        /*@
            loop invariant !(\at(x, Pre) < 100) ==> (y == \at(y, Pre) && x == \at(x, Pre));
            loop invariant y == \at(y, Pre);
            loop assigns x;
        */
        while (x < 100) {
            x = x + y;
        }
    }

    //@ assert y <= 0 || (y > 0 && x >= 100);
}
