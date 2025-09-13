
void foo(int x2, int x3) {
    int d1 = 1;
    int d2 = 1;
    int d3 = 1;
    int x1 = 1;

    /*@
    loop invariant x3 >= 0 || x1 < 0;
    loop invariant x2 >= 0 || x1 < 0;
    loop invariant x2 == x3;
    loop invariant x1 == x2 + d2 && x2 == x3 + d3;
    loop invariant d3 == 1;
    loop invariant d2 == 1;
    loop invariant d1 == 1;
    loop invariant \exists integer n; 0 <= n <= x3 && x3 == x3 - n*d3;
    loop invariant \exists integer n; 0 <= n <= x2 && x2 == x2 - n*d2;
    loop invariant \exists integer n; 0 <= n <= x1 && x1 == 1 - n*d1;
    loop invariant \exists integer k; 0 <= k && x2 == 1 - k * d2 && x3 == 1 - k * d3 && x1 == 1 - k * d1;
    loop invariant 0 <= x3;
    loop invariant 0 <= x3 + d3;
    loop invariant 0 <= x2;
    loop invariant 0 <= x2 + d2;
    loop invariant 0 <= x1;
    loop invariant 0 <= x1 + d1;
    loop invariant 0 < d3;
    loop invariant 0 < d2;
    loop invariant 0 < d1;
    loop invariant (x1 <= 1 && x2 <= 1) || (x1 > 0 && x2 > 0 && x3 > 0);
    loop assigns x3;
    loop assigns x2;
    loop assigns x1;
    */
    while(x1 > 0) {
        if(x2 > 0) {
            if(x3 > 0) {
                x1 = x1 - d1;
                x2 = x2 - d2;
                x3 = x3 - d3;
            }
        }
    }

    // @ assert x2 >= 0;
    //// @ assert x3 >= 0;
}
