
void foo40(int n) {
    int x = 0;

    /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
      loop invariant (0 < \at(n,Pre)) ==> (0 <= x <= n);
      loop invariant (!(0 < \at(n,Pre))) ==> ((x == 0) && (n == \at(n,Pre)));
      loop invariant n == \at(n,Pre);
      loop assigns x;
      loop variant n - x;
    */
    while (x < n) {
        x = (x + 1);
    }

    /* mask_1 */
}
