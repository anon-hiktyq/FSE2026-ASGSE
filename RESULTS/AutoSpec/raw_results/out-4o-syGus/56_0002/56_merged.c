/*@
requires n > 0;
*/
void foo(int n) {
  int c = 0;
  
  /*@
  loop invariant c > n ==> \forall integer k; 0 <= k < c ==> c > n;
  loop invariant c == n ==> c > 0;
  loop invariant c == n ==> \forall integer k; k < n;
  loop invariant c <= n;
  loop invariant c <= n || c == n+1;
  loop invariant c <= n + 1;
  loop invariant c < n || c > n;
  loop invariant c != n || c > 0;
  loop invariant c != n || c == 1;
  loop invariant c != n || c <= n;
  loop invariant c != n ==> c != n + 1;
  loop invariant \forall integer k; c > n ==> c == k + 1;
  loop invariant \forall integer k; 0 <= k <= c ==> k <= n + 1;
  loop invariant \forall integer i; 0 <= i < c ==> n > 0;
  loop invariant \forall integer i; 0 <= i < c ==> i < n;
  loop invariant \exists integer k; c == n+k && k != 0;
  loop invariant 0 <= n;
  loop invariant c == n ==> c <= n;
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
        c  = 1;
      }
    }
  }
  // post-condition
  if (c == n) {
    //@ assert n <= -1;
  }
}
