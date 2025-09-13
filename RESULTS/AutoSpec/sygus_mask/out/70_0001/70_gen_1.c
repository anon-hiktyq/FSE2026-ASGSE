/*@
requires n > 0;
*/
void foo(int n) {
    int x = 1;
    int y = 0;

    /*@
    loop invariant 1 <= x <= n + 1;
    loop invariant y == n - (x - 1);
    loop assigns x;
    loop assigns y;
    */
    while (x <= n) {
        y = n - x;
        x = x +1;
    }

}
