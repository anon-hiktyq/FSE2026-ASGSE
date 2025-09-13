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
  loop invariant y <= \old(y);
  loop invariant y - x == 0;
  loop invariant x == y;
  loop invariant x <= y;
  loop invariant x <= \old(x);
  loop invariant x - y == 0;
  loop invariant n <= y;
  loop invariant n <= x;
  loop invariant 0 <= y;
  loop invariant 0 <= x;
  loop invariant 0 <= n;
  loop assigns y;
  loop assigns x;
  ```c;
  ```;
  */
  while(x!=n) {
      x--;
      y--;
  }
  // @ assert y == n;
}
