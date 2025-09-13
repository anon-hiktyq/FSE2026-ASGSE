
void foo028() {
  int x = 0;
  int y = 0;
  int n = 0;
  
  /* >>> LOOP INVARIANT TO FILL <<< */
  
  /*@
    loop invariant x >= 0;
    loop invariant y == x;
    loop invariant n == 0;
    loop assigns x, y;
  */
  while(unknown()) {
      x++;
      y++;
  }
  
  /* >>> LOOP INVARIANT TO FILL <<< */
  
  /*@
    loop invariant y >= x - n;
    loop invariant x >= y;
    loop invariant n == 0;
    loop assigns x, y;
  */
  while(x != n) {
      x--;
      y--;
  }
  
  /*@ assert y == n; */
}
