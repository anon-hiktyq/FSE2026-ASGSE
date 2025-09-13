/*@
requires n > 0;
*/
void foo(int n) {
  int c = 0;

  /*@
  loop invariant c >= 1 || c == 0;
  loop invariant c >= 0 && c <= n;
  loop invariant c == n || c < n;
  loop invariant c == n ==> \forall integer k; 0 <= k < c ==> c > k;
  loop invariant c == 0 || c > 0;
  loop invariant c <= n && c >= 0;
  loop invariant c < n ==> \forall integer k; 0 <= k < n ==> k != n;
  loop invariant c + 1 <= n + 1;
  loop invariant c % n == 0 ==> c == n || c == 0;
  loop invariant c != n ==> c < n;
  loop invariant c != n ==> \exists integer m; 0 <= m < n && c == m;
  loop invariant \forall integer k; 0 <= k < c ==> k < n;
  loop invariant \forall integer k; 0 <= k < c ==> c <= n;
  loop invariant \exists integer k; 0 <= k <= n && c == k;
  loop invariant \exists integer k; 0 <= c;
  loop invariant (c == n) || (c >= 0 && c != n);
  loop invariant (c == n) || (c != n);
  loop invariant (c == n) ==> (n > 0);
  loop invariant (c < n) ==> (c >= 0);
  loop invariant (c != n) ==> (c != -1);
  loop invariant c == n ==> \forall integer k; 0 <= k < n ==> c == n;
  loop invariant c <= n;
  loop invariant c != n ==> c >= 0;
  loop invariant 0 <= c;
  loop invariant 0 < n;
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
