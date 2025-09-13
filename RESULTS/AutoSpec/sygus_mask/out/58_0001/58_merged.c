/*@
requires n > 0;
*/
void foo(int n) {
  int c = 0;
  
  /*@
  loop invariant c <= n;
  loop invariant \forall int k; 0 <= k <= c ==> (c != n || c == k);
  loop invariant \forall int k; 0 <= k < c ==> k < n;
  loop invariant \exists integer k; c == k && 0 <= k <= n;
  loop invariant \exists int k; k == c ==> (k < n ==> c == k + 1) || (k == n ==> c == 1);
  loop invariant \exists int k; k <= n ==> (c == n ==> k == 1);
  loop invariant \exists int k; c == k + 1 ==> k < n;
  loop invariant 0 <= c;
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
