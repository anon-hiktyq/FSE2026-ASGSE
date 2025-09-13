int unknown();

/*@
requires n > 0;
*/
void foo(int n) {
  int c = 0;
  
  /*@
  loop invariant c == n ==> \exists int k; k >= 0 && k < c;
  loop invariant c <= n;
  loop invariant c != n ==> \forall int k; 0 <= k < c ==> k < n;
  loop invariant \forall integer k; k < c ==> k < n;
  loop invariant \forall integer k; 0 <= k < c ==> k < n;
  loop invariant \forall int k; 0 <= k < c ==> c > k;
  loop invariant \exists integer k; k < c ==> k < n;
  loop invariant \exists int k; k == c ==> k != n;
  loop invariant 0 <= c;
  loop invariant 0 < n;
  loop invariant (c == n) ==> (\exists int k; k > 0 && k < n ==> c == k);
  loop invariant (c != n) ==> c < n;
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
