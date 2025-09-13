/*@
requires n > 0;
*/
void foo(int n) {
  int c = 0;

  /*@
  loop invariant c == n ==> n > 0;
  loop invariant c <= n;
  loop invariant c != n || unknown();
  loop invariant c != n || c >= 1;
  loop invariant c != n || c == 1;
  loop invariant c != n ==> c >= 0;
  loop invariant c != n ==> \exists integer k; c <= k < n;
  loop invariant \forall integer k; 0 <= k < n ==> c != n || c == 1;
  loop invariant \forall integer k; 0 <= k < c ==> c <= n;
  loop invariant 0 <= c;
  loop invariant 0 < n;
  loop invariant (c == n) ==> \false;
  loop assigns c;
  */
  while (unknown()) {
    if (unknown()) {
      if (c != n) {
        c = c + 1;
      }
    } else {
      if (c == n)
      {
        c = 1;
      }
    }
  }
  // post-condition
  if (c == n) {
    // @ assert n <= -1;
  }
}
