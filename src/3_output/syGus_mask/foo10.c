
/*@
    requires x >= 0 && x <= 2 && y <= 2 && y >= 0;
    */
    
void foo10(int x, int y) {

    /*@
        loop invariant (x >= 0 && y >= 0);
        loop assigns x, y;
    */
    while (unknown()) {
        x = x + 2;
        y = y + 2;
    }
}
