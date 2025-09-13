int main() {
  int x = -5000;
  int y = 0;
  
  /*@
  loop invariant x < 0 ==> y > 0;
  loop invariant x + y * (y - 1) / 2 == -5000;
  loop invariant y >= 0;
  loop invariant x < 0 || x >= 0;
  loop assigns x;
  loop assigns y;
  */
  while ((x < 0)) {
    x  = x + y;
    y  = y + 1;
  }
  // post-condition
  // @ assert y > 0;
}
