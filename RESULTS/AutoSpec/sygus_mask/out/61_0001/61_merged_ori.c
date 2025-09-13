/*@
requires n > 0;
*/
void foo(int n) {
  int c = 0;

  /*@
  loop invariant c == n ==> \exists integer k; k == 1; /* condition indicating when c resets */;
  loop invariant c == n ==> \exists boolean b; b == true;
  loop invariant c <= n;
  loop invariant c != n ==> c < n;
  loop invariant c != n ==> \exists boolean b; b == false;
  loop invariant \forall integer k; k < c ==> k < n;
  loop invariant \forall integer k; c == n ==> c == n;
  loop invariant \forall integer k; c == n ==> (k < c ==> k != n);
  loop invariant \forall integer k; c != n ==> c < n;
  loop invariant \forall integer k; 0 <= k < c ==> k < n;
  loop invariant \exists integer k; c == k && 0 <= k <= n;
  loop invariant \exists int k; k >= 0 && k <= n ==> (c == k);
  loop invariant 0 <= c;
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

}
