
/*@
    requires n > 0;
    ensures y == n;
*/
void foo005(int n, int x, int y) {
    x = n;
    y = 0;

    /* >>> LOOP INVARIANT TO FILL <<< */
    
    /*@
        loop invariant (\at(n,Pre) > 0) ==> (x >= n);
        loop invariant (\at(n,Pre) > 0) ==> (y <= n);
        loop invariant (!(\at(n,Pre) > 0)) ==> ((y == 0) && (x == \at(n,Pre)) && (n == \at(n,Pre)));
        loop invariant n == \at(n,Pre);
        loop assigns x, y;
    */
    while (x > 0) {
        x++;
        y--;
    }

    //@ assert y == n;
}
