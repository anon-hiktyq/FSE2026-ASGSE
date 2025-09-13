

void foo034(int n) {
  int x=0;
  int y=0;
  int i=0;
  int m=10;
  
 
  /*@
  loop invariant y == i / 2;;
  loop invariant y <= x;
  loop invariant y <= n / 2;
  loop invariant y <= i / 2;
  loop invariant x >= y && x <= 2 * y;
  loop invariant x == i;;
  loop invariant x <= i;
  loop invariant x <= 2 * y + 1;
  loop invariant x - y == i - y;
  loop invariant x - y == i - y * 2;
  loop invariant x - y == i - (i / 2);
  loop invariant x - y == i % 2;
  loop invariant x - y == (i % 2 == 0 ? 0 : 1);
  loop invariant m == 10;;
  loop invariant i <= n;;
  loop invariant i <= n;
  loop invariant i % 2 == 1 || x == 2 * y;
  loop invariant i % 2 == 1 ==> x == y * 2 + 1;
  loop invariant i % 2 == 1 ==> x == 2 * y + 1;
  loop invariant i % 2 == 0 ==> x == 2 * y;;
  loop invariant 2 * y <= x;
  loop invariant 0 <= n - i;
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

