

void foo034(int n) {
  int x=0;
  int y=0;
  int i=0;
  int m=10;
  
 
  /*@
  loop invariant 0 <= i <= n;
  loop invariant 0 <= x <= i;
  loop invariant x == y * 2 || x == y * 2 + 1;
  loop invariant y == i / 2;
  loop invariant \forall integer k; 0 <= k < i ==> (k % 2 == 0 ==> x == y * 2 + 1);
  loop invariant \forall integer k; 0 <= k < i ==> (k % 2 != 0 ==> x == y * 2 + 1);
  loop invariant y == i / 2;
  loop invariant y <= x;
  loop invariant y <= i / 2;
  loop invariant y * 2 <= x;
  loop invariant y * 2 <= x || y <= n / 2;
  loop invariant y * 2 <= x || x <= i + 1;
  loop invariant y * 2 <= x || i <= n;
  loop invariant y * 2 <= x || i <= n;
  loop invariant y * 2 <= x || 0 <= y;
  loop invariant x == y * 2 || x == y * 2 + 1;
  loop invariant x == i;
  loop invariant x == 2 * y || x == 2 * y + 1;
  loop invariant x <= i;
  loop invariant x <= i + 1;
  loop invariant x <= i + 1 || y <= n / 2;
  loop invariant x <= i + 1 || i <= n;
  loop invariant x <= 2 * y + 1;
  loop invariant x < i + 1;
  loop invariant x - y == i - y;
  loop invariant x - y == i - (i / 2);
  loop invariant m == 10;
  loop invariant i <= n || x <= i + 1;
  loop invariant i % 2 == 1 || x == 2 * y;
  loop invariant i % 2 == 1 ==> x == y * 2 + 1;
  loop invariant i % 2 == 1 ==> x == 2 * y + 1;
  loop invariant i % 2 == 0 ==> x == y * 2;
  loop invariant i % 2 == 0 ==> x == 2 * y;
  loop invariant i % 2 != 0 ==> x == y * 2 + 1;
  loop invariant \forall integer k; 0 <= k <= i ==> 2 * y <= x;
  loop invariant 2 * y <= x;
  loop invariant 0 <= y;
  loop invariant 0 <= y || y <= n / 2;
  loop invariant 0 <= y || x <= i + 1;
  loop invariant 0 <= y || i <= n;
  loop invariant 0 <= y || i <= n;
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

