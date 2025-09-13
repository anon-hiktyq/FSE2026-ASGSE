void main() {
  // variable declarations
  int x;
  int y;
  // pre-conditions
  x = 1;
  y = 0;
  // loop body
  /*@
  loop invariant y <= 1000;
  loop invariant x == y + 1;
  loop invariant x == y * (y - 1) / 2 + 1;
  loop invariant x == 1 + (y * (y - 1)) / 2;
  loop invariant x == (y * (y - 1)) / 2 + 1;
  loop invariant 0 <= y;
  loop assigns y;
  loop assigns x;
  */
  while (y < 1000) {
    x  = (x + y);
    y  = (y + 1);
  }

}
