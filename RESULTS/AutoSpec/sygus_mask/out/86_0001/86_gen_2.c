int main() {
  int x = -50;
  int y = 0;
  
  /*@
  loop invariant -50 <= x <= 0;
  loop invariant 0 <= y;
  loop assigns x;
  loop assigns y;
  */
  while (x < 0) {
    x  = x + y;
    y  = y + 1;
  }

}
