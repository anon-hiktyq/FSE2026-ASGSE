void main() {
  // variable declarations
  int x;
  int y;
  // pre-conditions
  x = 1;
  y = 0;
  // loop body
  /*@
  loop invariant y <= 100000;
  loop invariant x == y * (y - 1) / 2 + 1;
  loop invariant x == \sum_{k=0}^{y} k;
  loop invariant x == \sum_{k=0}^{y-1} k + 1;
  loop invariant x == 1 + \sum_{k=0}^{y-1} k;;
  loop invariant x == 1 + \sum_{k=0}^{y-1} k;
  loop invariant x == 1 + (y * (y - 1)) / 2; // Sum of first (y-1) natural numbers;
  loop invariant x == 1 + (y * (y - 1) / 2);
  loop invariant x == (y * (y - 1)) / 2 + 1;;
  loop invariant x == (y * (y - 1)) / 2 + 1;
  loop invariant 0 <= y;
  loop assigns y;
  loop assigns x;
  */
  while (y < 100000) {
    x  = x + y;
    y  = y + 1;
  }

}
