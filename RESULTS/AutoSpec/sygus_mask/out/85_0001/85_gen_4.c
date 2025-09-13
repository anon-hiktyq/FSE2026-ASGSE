int main() {
  int x = -15000;
  int y = 0;
  
  /*@
  loop invariant x < 0;
  loop invariant x == -15000 + y;
  loop assigns x;
  loop assigns y;
  */
  while (x < 0) {
    x  = x + y;
    y  = y + 1;
  }

}
