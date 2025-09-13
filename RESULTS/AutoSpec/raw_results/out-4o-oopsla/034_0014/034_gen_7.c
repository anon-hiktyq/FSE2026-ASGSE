

void foo034(int n) {
  int x=0;
  int y=0;
  int i=0;
  int m=10;
  
 
  /*@
  loop invariant x >= y;
  loop invariant x - y == i % 2;
  loop invariant 2 * y <= x <= 2 * y + 1;
  loop invariant n >= i;
  loop invariant y <= n / 2;
  loop invariant y == i / 2;
  loop invariant x == i;
  loop invariant m == 10;
  loop invariant i % 2 == 0 ==> x == 2 * y;
  loop invariant 0 <= i;
  loop assigns y;
  loop assigns x;
  loop assigns i;
  */
  while(i < n) {
    i++;
    x++;
    if(i%2 == 0) y++;
  }
  
  // @ assert (i == m) ==> (x == 2* y);*/
}

