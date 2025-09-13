
/*@
    requires x >= 0 && x <= 2 && y <= 2 && y >= 0;
    */
void foo9(int x,int y) {

    /*@
        loop invariant (x >= 0 && x <= 2 && y >= 0 && y <= 2) ==> (x - y == x - y); 
        loop invariant (x >= 0 && x <= 2 && y >= 0 && y <= 2) ==> (x % 2 == x % 2); 
        loop invariant (x >= 0 && x <= 2 && y >= 0 && y <= 2) ==> (y % 2 == y % 2);
        loop assigns x, y;
    */
    while (unknown()) {
        x = x + 2;
        y = y + 2;
    }
}
