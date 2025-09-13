void main() {
  // variable declarations
  int x;
  int y;
  // pre-conditions
  x = 1;
  y = 0;
  // loop body
  /*@
  loop invariant x >= y >= 1;
  loop invariant y <= 100000;
  loop invariant x == \sum(0, y-1, \lambda k; k) + 1;
  loop assigns x, y;
  */
  while (y < 100000) {
    x  = x + y;
    y  = y + 1;
  }
  // post-condition
  // @ assert x >= y >= 1;
}
