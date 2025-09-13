int fun(int x, int y) {
    int r = x;
    int d = 0;

    /*@
    loop invariant r < y;
    loop invariant r + d*y == x;
    loop invariant r + d * y == x;
    loop invariant d <= x;
    loop invariant d <= x / y;
    loop invariant 0 <= r;
    loop invariant 0 <= d;
    loop assigns r;
    loop assigns d;
    */
    while (r >= y) {
        printf("r = %d   d = %d   y = %d   x = %d\n", r, d, y, x);
        // Beginning
        r = r - y;
        d = d + 1;
        // ENd
        // @ assert r + d*y == x;
    }
    return d;
}