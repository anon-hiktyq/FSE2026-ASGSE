

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
  loop invariant y == m + (x - m > 0 ? (x - m) : 0);
  loop invariant x <= y;
  loop assigns x;
  loop assigns y;
  */
  while(x < n) {
    x++;
    if(x > m) y++;
  }
  // @ assert y==n;
}