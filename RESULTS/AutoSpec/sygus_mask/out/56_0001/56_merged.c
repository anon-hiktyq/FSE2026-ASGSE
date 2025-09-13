/*@
requires n > 0;
*/
void foo(int n) {
  int c = 0;
  
  /*@
  loop invariant \forall integer k; k < c ==> k <= n;
  loop invariant \forall integer k; 0 <= k < c ==> k <= n;
  loop invariant \exists int k; k >= 0 && k <= n ==> ( c > n || c == n );
  loop invariant \exists int k; k >= 0 && k <= c ==> k <= n;
  loop invariant \exists int k; c == k ==> k >= 0 && k <= n + 1;
  loop invariant \exists int k; c == k + 1 && k <= n;
  loop invariant 0 <= c;
  loop assigns c;
  */
  while (unknown()) {
    if (unknown()) {
      if (c > n) {
        c = c + 1;
      }
    } else {
      if (c == n) {
        c  = 1;
      }
    }
  }

}
