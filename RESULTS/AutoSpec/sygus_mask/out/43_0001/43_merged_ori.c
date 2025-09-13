int unknown();

/*@
requires n > 0;
*/
void foo(int n) {
  int c = 0;
  
  /*@
  loop invariant c == 0 ==> (c > n ==> c == 1);
  loop invariant c <= n + 1;
  loop invariant \forall integer k; 0 <= k < c ==> k <= n;
  loop invariant \forall integer k; 0 <= k < c ==> c > n;
  loop invariant \exists integer k; c == k && k <= n + 1;
  loop invariant 0 <= c;
  loop invariant 0 < n;
  loop assigns c;
  */
  while (unknown()) {
    if (unknown()) {
      if (c > n) {
        c  = c + 1;
      }
    } else {
      if (c == n) {
        c  = 1;
      }
    }
  }

}