
void foo16(int n) {
    int x = 0;
    int m = 0;

    /*@
      loop invariant (0 < \at(n,Pre)) ==> (0 <= x <= n);
      loop invariant (0 < \at(n,Pre)) ==> (((m == 0)&&(x == 0)&&(n == \at(n,Pre))) || (m == 0 || (0 <= m < x)));
      loop invariant (!(0 < \at(n,Pre))) ==> ((m == 0)&&(x == 0)&&(n == \at(n,Pre)));
      loop invariant n == \at(n,Pre);
      loop assigns x, m;
    */
    while (x < n) {
        if (unknown()) {
            m = x;
        }
        x = x + 1;
    }
}
