void main() {
  // variable declarations
  int x;
  int y;
  // pre-conditions
  x = 1;
  y = 0;
  // loop body
  /*@
  loop invariant 0 <= y <= 1000;
  loop invariant x == (y * (y - 1)) / 2 + 1;
  loop assigns x;
  loop assigns y;
  */
  while (y < 1000) {
    x  = (x + y);
    y  = (y + 1);
  }

}
