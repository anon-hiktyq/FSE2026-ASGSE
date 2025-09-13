

/*@
requires n >= 0;
requires m >= 0;
requires m < n;
*/
void foo019(int n, int m) {
 
  int x = 0; 
  int y = m;
 
  /*@
  loop invariant 0 <= x <= n;
  loop invariant m <= y <= n;
  loop invariant y == m + (x - m) * (x > m);
  loop assigns x, y;
  */
  while(x < n) {
    x++;
    if(x > m) y++;
  }
  // @ assert y==n;
}