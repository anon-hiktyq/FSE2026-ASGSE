/*@
requires n > 0;
*/
void foo(int n) {
  int c = 0;
  
  /*@
  loop invariant c == n ==> c == 0 || c == n;
  loop invariant c == n ==> \exists integer k; 0 <= k < n && !unknown();
  loop invariant c == n ==> \exists integer k; 0 <= k < c && !unknown();
  loop invariant c <= n;
  loop invariant c < n ==> \exists integer k; 0 <= k < c && unknown();
  loop invariant c < n ==> \exists integer k; 0 <= k < c && \exists integer j; 0 <= j < c && unknown();
  loop invariant c != n ==> c <= n-1;
  loop invariant c != n ==> c < n;
  loop invariant 0 <= c;
  loop invariant 0 < c;
  loop invariant (c == n && c <= n) || (c != n && c < n);
  loop assigns c;
  */
  while (unknown()) {
    if (unknown()) {
      if (c != n)
      {
        c = c + 1;
      }
    } else {
      if (c == n)
      {
        c = 1;
      }
    }
  }

}
