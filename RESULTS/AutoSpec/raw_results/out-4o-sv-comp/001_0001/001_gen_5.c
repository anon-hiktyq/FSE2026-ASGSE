
void foo001() {
    int x = 1;
    int y = 0;

   
    /*@
    loop invariant x >= y;
    loop invariant y <= 1000;
    loop invariant y >= 0;
    loop invariant x == \sum(0, y-1, \lambda integer k; k) + 1;
    loop assigns x, y;
    */
    while (y < 1000 ) {
        x = x + y;
        y = y + 1;
    }
    // @ assert x >= y;
}
