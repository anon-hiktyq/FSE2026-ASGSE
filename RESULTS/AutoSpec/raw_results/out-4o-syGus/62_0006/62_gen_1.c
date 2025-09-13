/*@
requires n > 0;
*/
void foo(int n) {
  int c = 0;
  
  /*@
  loop invariant c == 0 || c <= n;
  loop invariant c == n ==> 0 < n;
  loop invariant c == n ==> \exists integer k; 0 <= k < n;
  loop invariant c != n + 1 && c >= 0;
  loop invariant c >= 0 && c <= n + 1;
  loop invariant 0 < n;
  loop invariant c == 1 ==> n > 0;
  loop invariant c <= n;
  loop invariant c != n || (c == n && \exists integer k; 0 <= k < n+1);
  loop invariant c != n + 1;
  loop invariant 0 <= c;
  loop invariant 0 < n;
  loop invariant (c != n) ==> (c >= 0);
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
