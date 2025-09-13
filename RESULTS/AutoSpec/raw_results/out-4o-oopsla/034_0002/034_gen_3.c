

void foo034(int n) {
  int x=0;
  int y=0;
  int i=0;
  int m=10;
  
 
  /*@
  loop invariant 0 <= i <= n;
  loop invariant x == i;
  loop invariant y == i / 2;
  loop invariant x >= y;
  loop invariant x >= 2 * y;
  loop invariant m == 10;
  loop invariant i % 2 == 0 ==> x == 2 * y;
  loop invariant i % 2 == 0 ==> y == i / 2;
  loop invariant i % 2 == 1 ==> y == (i - 1) / 2;
  loop invariant (x == 2 * y) <==> (i % 2 == 0);
  loop invariant \forall integer k; 0 <= k < i ==> (k % 2 == 0 ==> x == 2 * y);
  loop invariant y == x / 2;
  loop invariant y == i / 2;
  loop invariant y <= x;
  loop invariant y <= x/2;
  loop invariant x == y + i - y;
  loop invariant x == y + (i - y);
  loop invariant x == i;
  loop invariant m == 10;
  loop invariant i % 2 == 1 ==> y == (i - 1) / 2;
  loop invariant i % 2 == 0 ==> y == i / 2;
  loop invariant i % 2 == 0 ==> x == 2 * y;
  loop invariant 2*y <= x;
  loop invariant 2 * y <= i;
  loop invariant 0 <= i;
  loop invariant (x == 2 * y) <==> (i % 2 == 0);
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

