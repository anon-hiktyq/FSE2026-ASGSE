
void foo001() {
    int x = 1;
    int y = 0;

   
    /*@
    loop invariant 0 <= y <= 1000;
    loop invariant x == y * (y - 1) / 2 + 1;
    loop invariant x >= y;
    loop assigns x, y;
    */
    while (y < 1000 ) {
        x = x + y;
        y = y + 1;
    }
    // @ assert x >= y;
}
