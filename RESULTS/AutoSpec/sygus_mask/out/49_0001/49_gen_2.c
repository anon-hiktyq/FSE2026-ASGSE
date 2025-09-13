int unknown();

/*@
requires n > 0;
*/
void foo(int n) {
  int c = 0;
  
  /*@
  loop invariant 0 <= c <= n;
  loop invariant c == n ==> unknown() == 0;
  loop invariant c != n ==> \forall integer k; 0 <= k < c ==> unknown() != 0;
  loop invariant c != n ==> \forall integer k; 0 <= k < c ==> unknown() != 0;
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
