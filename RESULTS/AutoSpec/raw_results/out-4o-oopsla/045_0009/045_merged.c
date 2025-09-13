
int unknown1();
int unknown2();
int unknown3();


void foo045(int flag) {
  int x = 0;
  int y = 0;
  int j = 0;
  int i = 0;

 
  /*@
  loop invariant y <= x;
  loop invariant x == y;
  loop invariant x == y || x == y + 1;
  loop invariant x == y || x + 1 == y;
  loop invariant j >= i || j == i - x;
  loop invariant j == i + (flag ? x : 0);
  loop invariant i <= j;
  loop invariant flag ==> j >= y;
  loop invariant flag ==> j == i + x;
  loop invariant 0 <= y;
  loop invariant 0 <= x;
  loop invariant 0 <= j;
  loop invariant 0 <= i;
  loop invariant !flag ==> j == i;
  loop assigns y;
  loop assigns x;
  loop assigns j;
  loop assigns i;
  */
  while (unknown1()) {
    x++;
    y++;
    i += x;
    j += y;
    if (flag) {
      j += 1;
    }
  }
  if (j >= i)
    x = y;
  else
    x = y + 1;

  int w = 1;
  int z = 0;
  
  /*@
  loop invariant z == w - 1;
  loop invariant z <= w;
  loop invariant y <= x;
  loop invariant x == y || x == y + 1;
  loop invariant w == z + 1;
  loop invariant 1 <= w;
  loop invariant 0 <= z;
  loop invariant 0 <= y;
  loop invariant 0 <= x;
  loop assigns z;
  loop assigns y;
  loop assigns x;
  loop assigns w;
  */
  while (unknown2()) {
   
    /*@
    loop invariant z == x + y;
    loop invariant z + 1 <= w;
    loop invariant z % 2 == 1 || y <= x;
    loop invariant z % 2 == 0 || w % 2 == 1;
    loop invariant z % 2 == 0 ==> y >= x;
    loop invariant z % 2 == (w % 2 == 1 ? 1 : 0);
    loop invariant y <= w;
    loop invariant y - x <= 1;
    loop invariant y + x <= z;
    loop invariant y % 2 == z % 2;
    loop invariant x <= w;
    loop invariant x - y <= 1;
    loop invariant x + y == z;
    loop invariant x % 2 == w % 2;
    loop invariant w == x + y + 1;
    loop invariant w % 2 == z % 2;
    loop invariant w % 2 == 1 ==> x >= y;
    loop invariant w % 2 == 0 || x >= y;
    loop invariant \forall integer k; 0 <= k <= z ==> x >= y;
    loop invariant \forall integer k; 0 <= k <= z ==> w == k + 1;
    loop invariant \forall integer k; 0 <= k <= z ==> (k % 2 == 0 ==> y >= k / 2);
    loop invariant \forall integer k; 0 <= k <= y ==> k % 2 == 1 || k % 2 == 0;
    loop invariant \forall integer k; 0 <= k <= x ==> k % 2 == 1 || k % 2 == 0;
    loop invariant \forall integer k; 0 <= k < y ==> k % 2 != z % 2;
    loop invariant \forall integer k; 0 <= k < x ==> k % 2 == w % 2;
    loop invariant \exists integer k; 0 <= k <= z && w == k + 1;
    loop invariant 0 < w;
    loop invariant (x - y) % 2 == 0;
    loop invariant z <= w;
    loop invariant y <= x;
    loop invariant x == y || x == y + 1;
    loop invariant w == z + 1;
    loop invariant 1 <= w;
    loop invariant 0 <= z;
    loop invariant 0 <= y;
    loop invariant 0 <= x;
    loop assigns y;
    loop assigns x;
    */
    while (unknown3()) {
      if (w % 2 == 1)
        x++;
      if (z % 2 == 0)
        y++;
    }
    z = x + y;
    w = z + 1;
  }
  // @ assert x == y;
}