int main() {
  int x = -15000;
  int y = 0;
  
  /*@
  loop invariant x < 0 ==> y > 0;
  loop invariant y >= 0;
  loop invariant x + y * (y - 1) / 2 == -15000;
  loop invariant x <= -15000 + y * (y - 1) / 2;
  loop assigns x, y;
  */
  while (x < 0) {
    x  = x + y;
    y  = y + 1;
  }
  // post-condition
  // @ assert y > 0;
}
