int fun(int x, int y) {
    int r = x;
    int d = 0;

   
    /*@
    loop invariant r >= 0;
    loop invariant r + d * y == x;
    loop invariant d >= 0;
    loop invariant r >= y ==> r - y >= 0;
    loop assigns r;
    loop assigns d;
    */
    while (r >= y) {
        printf("r = %d   d = %d   y = %d   x = %d\n", r, d, y, x);
        // Beginning
        r = r - y;
        d = d + 1;
        // ENd
     
    }
    return d;
}