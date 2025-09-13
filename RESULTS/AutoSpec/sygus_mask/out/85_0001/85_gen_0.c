int main() {
  int x = -15000;
  int y = 0;
  
  /*@
  loop invariant x < 0;
  loop assigns y;
  loop assigns x;
  */
  while (x < 0) {
    x  = x + y;
    y  = y + 1;
  }

}
