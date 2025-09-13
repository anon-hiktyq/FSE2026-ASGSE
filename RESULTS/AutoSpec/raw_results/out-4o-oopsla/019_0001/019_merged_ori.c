

/*@
requires n >= 0;
requires m >= 0;
requires m < n;
*/
void foo019(int n, int m) {
 
  int x = 0; 
  int y = m;
 
  /*@
  loop invariant y == x || y == x + m;
  loop invariant y == m + (x > m ? x - m : 0);
  loop invariant y == m + (x - m);
  loop invariant y == m + (x - m) * (x > m);
  loop invariant y == m + (x - m > 0 ? x - m : 0);
  loop invariant y == m + (x - m > 0 ? (x - m) : 0);
  loop invariant y <= x;
  loop invariant y <= n;
  loop invariant x >= m ==> y == x;
  loop invariant x > m ==> y == x;
  loop invariant x <= y;
  loop invariant x <= n;
  loop invariant x <= m ==> y == m;
  loop invariant m <= y;
  loop invariant 0 <= x;
  loop assigns y;
  loop assigns x;
  */
  while(x < n) {
    x++;
    if(x > m) y++;
  }
  // @ assert y==n;
}