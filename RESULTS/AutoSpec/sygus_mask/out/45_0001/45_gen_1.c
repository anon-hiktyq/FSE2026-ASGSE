int unknown();

/*@
requires n > 0;
*/
void foo(int n) {
  int c = 0;
  
  /*@
  loop invariant c >= 0;
  loop invariant c <= n;
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
