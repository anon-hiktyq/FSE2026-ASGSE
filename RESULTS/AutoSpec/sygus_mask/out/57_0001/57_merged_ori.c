/*@
requires n > 0;
*/
void foo(int n) {
  int c = 0;
  
  /*@
  loop invariant c == 0 || c == n || c > n;
  loop invariant c <= n + 1;
  loop invariant \forall integer k; k < c ==> (k <= n);
  loop invariant \forall integer k; 0 <= k < c ==> c > n ==> (c > k);
  loop invariant \exists integer k; c == k && k >= 0 && k <= n + 1;
  loop invariant \exists integer k; c == k && k <= n ==> k >= 0;
  loop invariant \exists int k; k >= 0 && k <= n ==> (c == k || c == k + 1);
  loop invariant \exists boolean b; b == (c > n) ==> (c == n + 1);
  loop invariant 0 <= c;
  loop invariant 0 < n;
  loop assigns c;
  */
  while (unknown()) {
    if (unknown()) {
      if (c > n) {
        c = c + 1;
      }
    } else {
      if (c == n) {
        c = 1;
      }
    }
  }


}
