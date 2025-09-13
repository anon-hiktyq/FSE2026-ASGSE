int fun(int x, int y) {
    int r = x;
    int d = 0;

   
    /*@
    loop invariant r >= y ==> r - y >= 0;
    loop invariant r >= y ==> d >= 0;
    loop invariant r >= y ==> (d + 1) * y <= x;
    loop invariant r + d * y == x;
    loop invariant d * y + r == x;
    loop invariant \exists int k; k >= 0 && k <= d && r + d * y == x;
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
     
    }
    return d;
}