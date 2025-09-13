int unknown();





void foo028() {
  int x = 0;
  int y = 0;
  int n = 0;
 
  /*@
  loop invariant y == x;
  loop invariant x == y;
  loop invariant n <= y;
  loop invariant n <= x;
  loop invariant 0 <= y;
  loop invariant 0 <= x;
  loop assigns y;
  loop assigns x;
  */
  while(unknown()) {
      x++;
      y++;
  }
 
  /*@
  /*@
    loop invariant x >= n;
    loop invariant y - x == 0;
    loop invariant x >= 0;
    loop invariant y >= 0;
    loop assigns x;
    loop assigns y;
    */
  */
  while(x!=n) {
      x--;
      y--;
  }
  // @ assert y == n;
}
