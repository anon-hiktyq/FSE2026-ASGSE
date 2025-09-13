void main() {
  // variable declarations
  int x;
  int y;
  // pre-conditions
  x = 1;
  y = 0;
  // loop body
  /*@
  loop invariant x >= y;
  loop invariant y >= 0;
  loop invariant x >= 1;
  loop invariant 1 <= y <= 100000;
  loop assigns x, y;
  loop variant 100000 - y;
  */
  while (y < 100000) {
    x  = x + y;
    y  = y + 1;
  }
  // post-condition
  // @ assert x >= y >= 1;
}
