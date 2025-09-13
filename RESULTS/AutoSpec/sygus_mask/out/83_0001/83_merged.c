int main() {
  int x = -5000;
  int y = 0;
  
  /*@
  loop invariant x < 0;
  loop invariant x + y == -5000;
  loop invariant 0 <= y;
  loop assigns y;
  loop assigns x;
  */
  while ((x < 0)) {
    x  = x + y;
    y  = y + 1;
  }

}
