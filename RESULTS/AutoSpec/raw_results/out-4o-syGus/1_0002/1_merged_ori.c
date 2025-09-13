void main() {
  // variable declarations
  int x;
  int y;
  // pre-conditions
  x = 1;
  y = 0;
  // loop body
  /*@
  loop invariant y <= x;
  loop invariant y <= 100000;
  loop invariant x == \sum(0, y-1, \lambda k; k) + 1;
  loop invariant x == \sum(0, y-1, \lambda k; 1 + k);
  loop invariant x == \sum(0, y - 1, \lambda k. k) + 1; // x is the sum of all integers from 0 to (y-1) plus 1;
  loop invariant x == (y * (y - 1)) / 2 + 1;
  loop invariant 100000 - y;
  loop invariant 1 <= y;
  loop invariant 1 <= x;
  loop invariant 0 <= y;
  loop assigns y;
  loop assigns x;
  */
  while (y < 100000) {
    x  = x + y;
    y  = y + 1;
  }
  // post-condition
  // @ assert x >= y >= 1;
}
