void main() {
  // variable declarations
  int x;
  int y;
  // pre-conditions
  x = 1;
  y = 0;
  // loop body
  /*@
  loop invariant y == 0 + (1 + 2 + ... + (y - 1));
  loop invariant y <= 1000;
  loop invariant x == y + 1;
  loop invariant x == y * (y - 1) / 2 + 1;
  loop invariant x == y * (y + 1) / 2; // sum of the first y natural numbers;
  loop invariant x == y * (y + 1) / 2; // sum of first y natural numbers;
  loop invariant x == 1 + \sum_{k=0}^{y-1} k; // Sum of first y natural numbers;
  loop invariant x == 1 + \sum_{k=0}^{y-1} k;
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
