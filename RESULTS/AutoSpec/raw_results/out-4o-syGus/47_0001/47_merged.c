int unknown();

/*@
requires n > 0;
*/
void foo(int n) {
  int c = 0;
  
  /*@
  loop invariant c == 0 || c >= 1;
  loop invariant c <= n;
  loop invariant \exists integer k; 0 <= k <= n && c == k;
  loop invariant 0 <= c;
  loop invariant 0 < n;
  loop assigns c;
  */
  while (unknown()) {
      if (unknown()) {
        if (c != n) {
          c  = c + 1;
        }
      } else {
        if (c == n) {
          c = 1;
        }
      }
  }
  // post-condition
  if (c < 0) {
    if (c > n) {
      //@ assert c == n;
    }
  }
}
