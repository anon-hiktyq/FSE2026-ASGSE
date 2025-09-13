int unknown();

/*@
requires n > 0;
*/
void foo(int n) {
  int c = 0;
  
  /*@
  loop invariant \exists integer k; k >= 0 && k <= n ==> (c == n ==> c == 1) || (c > n ==> c == k + 1);
  loop invariant \exists integer k; c == k + 1 ==> ( k < n ==> c > n );
  loop invariant \exists integer k; 0 <= k;
  loop invariant 0 <= c;
  loop invariant 0 < n;
  loop invariant (c == n) ==> (c == 1) || (c > n);
  loop invariant (c == n) ==> (c == 1 || c > n);
  loop assigns c;
  */
  while (unknown()) {
    if ( unknown() ) {
      if (c > n) {
        c  = c + 1;
      }
    } else {
      if (c == n) {
        c = 1;
      }
    }
  }

}
