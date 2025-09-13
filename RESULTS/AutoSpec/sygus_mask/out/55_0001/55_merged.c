/*@
requires n > 0;
*/
void foo(int n) {
  int c = 0;
  
  /*@
  loop invariant c <= n + 1;
  loop invariant \forall integer k; k < c ==> k <= n;
  loop invariant \exists integer k; c == n ==> c == 1;
  loop invariant \exists integer k; c == k && k > n ==> c == k + 1;
  loop invariant \exists int k; k >= 0 && k <= n ==> (c == k || c == n + 1);
  loop invariant \exists int k; 0 <= k < c ==> k <= n;
  loop invariant \exists boolean b; (b ==> c > n) || (!b ==> c == n);
  loop invariant 0 <= c;
  loop invariant 0 < n;
  loop invariant (c > n) ==> (c > n + 1);
  loop invariant (c == n) ==> (c >= 1);
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
