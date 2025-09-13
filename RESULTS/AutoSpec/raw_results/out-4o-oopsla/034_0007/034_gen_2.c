

void foo034(int n) {
  int x=0;
  int y=0;
  int i=0;
  int m=10;
  
 
  /*@
  loop invariant x == i;
  loop invariant y == x / 2 || y == (x - 1) / 2;
  loop invariant y <= i / 2;
  loop invariant \forall integer k; 0 <= k < i ==> (k % 2 == 0 ==> x >= 2 * y);
  loop invariant x <= n;
  loop invariant i <= n;
  loop invariant m == 10;
  loop invariant y == x / 2;
  loop invariant y == x / 2 || y == (x - 1) / 2;
  loop invariant y == i / 2;
  loop invariant y <= x;
  loop invariant y <= x / 2;
  loop invariant y <= i/2;
  loop invariant y <= i / 2;
  loop invariant x == i;
  loop invariant x == 2*y || x == 2*y + 1;
  loop invariant x == 2 * y || x == 2 * y + 1;
  loop invariant x <= i;
  loop invariant m == 10;
  loop invariant i == x;
  loop invariant i % 2 == x % 2;
  loop invariant i % 2 == 0 ==> x == 2 * y;
  loop invariant \forall integer k; 0 <= k < n ==> (k % 2 == 0 ==> x >= 2 * y);
  loop invariant 2 * y <= i;
  loop invariant 0 <= y;
  loop invariant 0 <= x;
  loop invariant 0 <= i;
  loop invariant (i % 2 == 0) ==> (x == 2*y);
  loop invariant (i % 2 == 0) ==> (x == 2 * y);
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

