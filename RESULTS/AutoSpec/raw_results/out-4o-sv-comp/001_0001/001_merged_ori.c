
void foo001() {
    int x = 1;
    int y = 0;

   
    /*@
    loop invariant y <= x;
    loop invariant y <= 1000;
    loop invariant x == y*(y-1)/2 + 1;
    loop invariant x == y * (y - 1) / 2 + 1;
    loop invariant x == \sum(0, y-1, \lambda integer k; k) + 1;;
    loop invariant x == \sum(0, y-1, \lambda integer k; k) + 1;
    loop invariant x == (y * (y - 1)) / 2 + 1;
    loop invariant 0 <= y;
    loop assigns y;
    loop assigns x;
    */
    while (y < 1000 ) {
        x = x + y;
        y = y + 1;
    }
    // @ assert x >= y;
}
