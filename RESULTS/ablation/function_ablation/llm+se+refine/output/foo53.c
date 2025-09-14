
/*@
    requires l > 0;
    requires n > l;
*/
void foo53(int n, int l) {
  int i, k;

  k = 1;

  /* >>> LOOP INVARIANT TO FILL <<< */
  /*@
    loop invariant (1 < \at(n,Pre)) ==> (\forall integer i; (l <= i < n) ==> (1 <= i));
    loop invariant (1 < \at(n,Pre)) ==> (1 <= k <= n + 1);
    loop invariant (!(1 < \at(n,Pre))) ==> ((k == 1) && (l == \at(l,Pre)) && (n == \at(n,Pre)));
  */
  for (k = 1; k < n; k++) {
    i = l;

    /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
      loop invariant l > 0;
      loop invariant 1 <= k <= n;
    */
    for (i = l; i < n; i++) {
    }
  }

  /*@ assert \forall integer i; (l <= i < n) ==> (1 <= i); */
}
