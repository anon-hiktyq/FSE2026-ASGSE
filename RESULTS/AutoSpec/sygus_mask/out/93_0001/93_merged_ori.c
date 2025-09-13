/*@
requires n >= 0;
*/
void foo(int n) {
  int i = 0;
  int x = 0;
  int y = 0;
    
  /*@
  loop invariant x == 2*(y-x);
  loop invariant x + 2*y == i;
  loop invariant x + 2*y == 3*i;
  loop invariant x + 2*y == 2*i;
  loop invariant i <= n;
  loop invariant 0 <= i;
  loop assigns y;
  loop assigns x;
  loop assigns i;
  */
  while (i < n) {
    i = i + 1;
    if (unknown()) {
      x  = x + 1;
      y  = y + 2;
    } else {
      x  = x + 2;
      y  = y + 1;
    }
  }

}
