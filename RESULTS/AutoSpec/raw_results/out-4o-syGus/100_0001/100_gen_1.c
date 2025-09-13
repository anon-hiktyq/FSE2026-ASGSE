/*@
requires n >= 0;
*/
void foo(int n) {
  int x = n;
  int y = 0;
    
  /*@
  loop invariant x >= 0;
  loop invariant y >= 0;
  loop invariant x + y == n;
  loop assigns x;
  loop assigns y;
  */
  while (x > 0) {
    y  = y + 1;
    x  = x - 1;
  }
  // post-condition
  // @ assert y == n;
}