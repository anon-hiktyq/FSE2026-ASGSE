int main() {
  int x = -50;
  int y = 0;

  /*@
  loop invariant x < 0;
  loop invariant y >= 0;
  loop invariant y == -x; 
  loop assigns x;
  loop assigns y;
  */
  while (x < 0) {
    x  = x + y;
    y  = y + 1;
  }

}
