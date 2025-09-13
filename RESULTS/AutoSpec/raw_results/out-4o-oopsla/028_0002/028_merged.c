int unknown();





void foo028() {
  int x = 0;
  int y = 0;
  int n = 0;
 
  /*@
  loop invariant y == x;
  loop invariant y <= x;
  loop invariant x == y;
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
 
  /*@
  loop invariant y == x;
  loop invariant y <= x;
  loop invariant y - x == 0;
  loop invariant x == y;
  loop invariant x <= y;
  loop invariant x - y == 0;
  loop assigns y;
  loop assigns x;
  */
  while(x!=n) {
      x--;
      y--;
  }
  //@ assert y == n;
}
