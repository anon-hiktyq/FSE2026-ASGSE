/*@
requires n > 0;
*/
void foo(int n) {
  int c = 0;
  
  /*@
  loop invariant c >= 0;
  loop invariant c <= n + 1;
  loop invariant \exists boolean b; b == (c > n) ==> (c == n + 1);
  loop invariant \forall integer k; 0 <= k < c ==> c > n ==> (c > k);
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
