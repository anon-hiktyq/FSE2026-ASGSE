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
  loop invariant x == 1 + (y * (y - 1)) / 2; // Sum of first (y-1) natural numbers
  loop assigns x;
  loop assigns y;
  */
  while (y < 100000) {
    x  = x + y;
    y  = y + 1;
  }

}
