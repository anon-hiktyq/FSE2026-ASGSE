/*@
requires n > 0;
*/
void foo(int n) {
  int c = 0;
  
  /*@
  loop invariant c >= 0;
  loop invariant c <= n;
  loop invariant \exists int k; c == k + 1 ==> k < n;
  loop invariant \forall int k; 0 <= k < c ==> k < n;
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
