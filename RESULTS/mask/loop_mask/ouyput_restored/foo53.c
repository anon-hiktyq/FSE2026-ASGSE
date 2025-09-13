
/*@
    requires l > 0;
    requires n > l;
    */
    
void foo53(int n, int l) {
  int i, k;

  k = 1;

  /*@
    loop invariant l > 0;
    loop invariant n > l;
    */
  for (k = 1; k < n; k++) {
    i = l;

    /*@
      loop invariant l > 0;
      loop invariant n > l;
      loop invariant l <= i <= n;
      */
    for (i = l; i < n; i++) {
    }
  }

  /*@ assert \forall integer i; (l <= i < n) ==> (1 <= i); */
}
