int unknown();





void foo028() {
  int x = 0;
  int y = 0;
  int n = 0;
 
  /*@
  loop invariant y == x;
  loop invariant y == n;
  loop invariant y == n - x;
  loop invariant y <= x;
  loop invariant x == y;;
  loop invariant x == y;
  loop invariant x <= n;
  loop invariant 0 <= y;
  loop invariant 0 <= x;
  loop assigns y;
  loop assigns x;
  loop assigns n;
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
