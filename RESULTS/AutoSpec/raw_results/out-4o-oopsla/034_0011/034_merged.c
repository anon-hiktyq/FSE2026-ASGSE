

void foo034(int n) {
  int x=0;
  int y=0;
  int i=0;
  int m=10;
  
 
  /*@
  loop invariant y <= n / 2 || x <= i;
  loop invariant y <= n / 2 || x <= 2 * y + 1;
  loop invariant y <= n / 2 || 0 <= x;
  loop invariant x <= i;
  loop invariant x <= i || i <= n;
  loop invariant x <= i || 0 <= x;
  loop invariant x <= 2 * y + 1;
  loop invariant x <= 2 * y + 1 || x <= i;
  loop invariant x <= 2 * y + 1 || i <= n;
  loop invariant x <= 2 * y + 1 || 0 <= x;
  loop invariant i <= n || 0 <= x;
  loop invariant \forall integer k; 0 <= k < i ==> k % 2 == 1 ==> y >= k / 2;
  loop invariant \forall integer k; 0 <= k < i ==> k % 2 == 0 ==> x >= k;
  loop invariant \forall integer k; 0 <= k < i ==> (k % 2 == 1 ==> x > k);
  loop invariant 2 * y <= x && x <= 2 * y + 1;
  loop invariant 0 <= x;
  loop invariant (i % 2 == 1) ==> (x == 2 * y + 1);
  loop invariant (i % 2 == 0) ==> (x == 2 * y);
  loop invariant y == x / 2;
  loop invariant y == i / 2;
  loop invariant y == \floor(i/2);
  loop invariant y == \floor(i / 2);
  loop invariant y <= x;
  loop invariant y <= x / 2;
  loop invariant x == i;
  loop invariant x == 2 * y || x == 2 * y + 1;
  loop invariant i % 2 == 1 ==> x == 2 * y + 1;
  loop invariant i % 2 == 0 ==> x == 2 * y;
  loop invariant \forall integer k; 0 <= k < i ==> (k % 2 == 1 ==> x >= k);
  loop invariant \forall integer k; 0 <= k < i ==> (k % 2 == 0 ==> y >= k / 2);
  loop invariant \floor(i / 2) == y;
  loop invariant 2*y <= x;
  loop invariant 2 * y <= x;
  loop invariant 0 <= y;
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
  
  //@ assert (i == m) ==> (x == 2* y);*/
}

