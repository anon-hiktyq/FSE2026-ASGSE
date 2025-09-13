int unknown();





void foo028() {
  int x = 0;
  int y = 0;
  int n = 0;
 
  /*@
  loop invariant x == y;
  loop invariant y >= 0;
  loop assigns x;
  loop assigns y;
  */
  while(unknown()) {
      x++;
      y++;
  }
 
  while(x!=n) {
      x--;
      y--;
  }
  // @ assert y == n;
}
