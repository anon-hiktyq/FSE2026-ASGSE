
/*@
    requires n >= 0;
    ensures \true;
*/
void foo133(int n) {

    int x = 0;

    /*@
      loop invariant 0 <= x <= n;
      loop invariant n == \at(n, Pre);
      loop assigns x;
    */
    while (x < n) {
        x = x + 1;
    }
}
