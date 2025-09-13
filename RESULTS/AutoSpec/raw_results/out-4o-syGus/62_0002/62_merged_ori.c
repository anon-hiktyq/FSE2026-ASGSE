/*@
requires n > 0;
*/
void foo(int n) {
  int c = 0;
  
  /*@
  loop invariant c > 0 ==> c <= n;
  loop invariant c == n || c == 0 || c == 1;
  loop invariant c == n || c < n;
  loop invariant c == n ==> unknown();
  loop invariant c < n || c == n;
  loop invariant c < n || c == n && c == 1;
  loop invariant c < n || c == 1;
  loop invariant c != n || c > 0;
  loop invariant c != n || \exists integer k; c > 0;
  loop invariant c != n ==> c >= 0;
  loop invariant c != n ==> c >= 0 && c <= n;
  loop invariant c != n ==> c <= n-1;
  loop invariant c != n ==> \exists integer k; 0 <= k < n;
  loop invariant c != n ==> 0 < c <= n;
  loop invariant \forall integer k; 0 <= k <= n ==> c != k || c == k;
  loop invariant \forall integer k; 0 <= k < c ==> c <= n;
  loop invariant -1 < n;
  loop invariant c == n ==> c > 0;
  loop invariant c <= n;
  loop invariant c != n || c == n;
  loop invariant c != n || \forall integer k; c > 0;
  loop invariant c != n ==> c == 0 || c <= n;
  loop invariant 0 <= c;
  loop invariant 0 < n;
  loop assigns c;
  */
  while (unknown()) {
    if (unknown()) {
      if (c != n)
      {
        c = c + 1;
      }
    } else {
      if (c == n)
      {
        c = 1;
      }
    }
  }
  // post-condition
  if (n > -1){
    // @ assert c != n;
  }

}
