/*@
requires n > 0;
*/
void foo(int n) {
  int c = 0;
  
  /*@
  loop invariant -1 <= c <= n + 1;
  loop invariant c == n ==> \forall integer k; 0 <= k < n ==> k != c;
  loop assigns c;
  */
  while (unknown()) {
    if (unknown()) {
      if (c > n) {
        c = c + 1;
      }
    } else {
      if (c == n) {
        c  = 1;
      }
    }
  }
  // post-condition
  if (c == n) {
    // @ assert n <= -1;
  }
}
