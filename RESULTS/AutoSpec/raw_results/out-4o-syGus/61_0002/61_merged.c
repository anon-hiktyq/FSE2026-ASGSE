/*@
requires n > 0;
*/
void foo(int n) {
  int c = 0;

  /*@
  loop invariant c >= 0 && c <= n;
  loop invariant c == n ==> n > 0;
  loop invariant c == n ==> c >= 1;
  loop invariant c == n ==> \forall integer k; 0 <= k < n ==> c != k;
  loop invariant c == n ==> \forall integer i; i < n ==> i < n;
  loop invariant c <= n && c >= 0;
  loop invariant c < n+1;
  loop invariant c < n || c == n;
  loop invariant c != n ==> c <= n-1;
  loop invariant c != n ==> c < n;
  loop invariant \forall integer k; 0 <= k <= c ==> k < n || k == c;
  loop invariant \forall integer k; 0 <= k < c ==> k < n;
  loop invariant \exists integer x; 0 <= x <= n && c == x;
  loop invariant \exists integer k; 0 <= k <= n && c == k;
  loop invariant \exists integer k; 0 <= k < n && c == k;
  loop invariant 1 <= n;
  loop invariant c <= n;
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
