/*@
requires n > 0;
*/
void foo(int n) {
  int c = 0;
  
  /*@
  loop invariant c >= 0;
  loop invariant c <= n;
  loop invariant c != n ==> \exists integer k; k >= 0 && k < c;
  loop invariant c == n ==> \forall integer k; 0 <= k < n ==> c == n;
  loop assigns c;
  */
  while (unknown()) {
    if (unknown()) {
      if (c != n) {
        c = c + 1;
      }
    } else {
      if (c == n) {
        c = 1;
      }
    }
  }

}
