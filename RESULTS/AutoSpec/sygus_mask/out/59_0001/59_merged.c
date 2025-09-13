/*@
requires n > 0;
*/
void foo(int n) {
  int c = 0;
  
  /*@
  loop invariant c == n ==> \forall integer k; 0 <= k < n ==> c == n;
  loop invariant c == n ==> (\exists int k; k >= 1 && k <= c);
  loop invariant c <= n;
  loop invariant c != n ==> \forall int k; 0 <= k < c ==> k < n;
  loop invariant \forall integer k; 0 <= k < c ==> k <= n;
  loop invariant \forall integer k; 0 <= k < c ==> k < n;
  loop invariant \forall integer k; 0 <= k < c ==> c >= k;
  loop invariant \exists integer k; k >= 0 && k <= n ==> (c == k);
  loop invariant \exists integer k; k < c ==> (k < n ==> c == k + 1);
  loop invariant \exists integer k; 0 <= k < n ==> c != n;
  loop invariant \exists integer k; 0 <= k < c ==> k < n;
  loop invariant 0 <= c;
  loop invariant 0 < n;
  loop invariant (c == n) ==> \exists integer k; 0 <= k < n && c == k + 1;
  loop assigns n;
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
