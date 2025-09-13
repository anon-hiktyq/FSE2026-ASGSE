void main() {
  // variable declarations
  int x;
  int y;
  // pre-conditions
  x = 1;
  y = 0;
  // loop body
  /*@
  loop invariant 0 <= y <= 100000;
  loop invariant x == 1 + \sum_{k=0}^{y-1} k;
  loop invariant x == \sum_{k=0}^{y} k;
  loop assigns x;
  loop assigns y;
  */
  while (y < 100000) {
    x  = x + y;
    y  = y + 1;
  }

}
