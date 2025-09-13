int main() {
  int x = -50;
  int y = 0;

  /*@
  loop invariant x < 0 || x >= 0;
  loop invariant y >= 0;
  loop invariant x == -50 + (\sum integer k; 0 <= k < y ==> k);
  loop invariant x < 0 ==> y < 51;
  loop assigns x, y;
  */
  while (x < 0) {
    x  = x + y;
    y  = y + 1;
  }
  // post-condition
  // @ assert y > 0;
}
