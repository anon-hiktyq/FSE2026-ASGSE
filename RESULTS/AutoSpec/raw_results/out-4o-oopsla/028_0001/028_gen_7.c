int unknown();





void foo028() {
  int x = 0;
  int y = 0;
  int n = 0;
 
  /*@
  loop invariant x == y; 
  loop invariant 0 <= x;
  loop invariant 0 <= y;
  loop assigns x, y;
  
  loop invariant x == y;
  loop invariant x >= 0;
  loop invariant y >= 0;
  loop invariant y == x;
  loop invariant y == n;
  loop assigns x, y;
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
