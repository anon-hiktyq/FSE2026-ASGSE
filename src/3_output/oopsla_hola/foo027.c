
/*@
    requires l > 0;
*/
void foo027(int l,int n) {
  int i, k;

  k = 1;

  /* >>> LOOP INVARIANT TO FILL <<< */
  /*@
    loop invariant !(1 < \at(n,Pre)) ==> ((k == 1) && (n == \at(n,Pre)) && (l == \at(l,Pre)));
    loop assigns k;
  */
  for (k = 1; k < n; k++) {
    i = l;

    /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    */
    for (i = l; i < n; i++) {

    }

    /*@ assert \forall integer j; (l <= j < n) ==> (1 <= k); */
  }
}
