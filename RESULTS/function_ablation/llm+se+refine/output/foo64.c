
void foo64() {
  int x = 0;
  int y = 0;
  int n = 0;

  /*@
    loop invariant x == y;
    loop invariant x >= 0;
    loop invariant n == 0;
    loop assigns x, y;
    loop variant 0;
  */
  while(unknown()) {
      x++;
      y++;
  }

  /*@
    loop invariant x >= n;
    loop invariant x == y;
    loop assigns x, y;
    loop variant x - n;
  */
  while(x != n) {
      x--;
      y--;
  }

  /*@ assert y == n; */
}
