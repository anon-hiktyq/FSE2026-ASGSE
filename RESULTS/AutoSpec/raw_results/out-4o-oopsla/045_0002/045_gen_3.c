
int unknown1();
int unknown2();
int unknown3();


void foo045(int flag) {
  int x = 0;
  int y = 0;
  int j = 0;
  int i = 0;

 
  /*@
  loop invariant y == x;
  loop invariant y <= x;
  loop invariant x == y;
  loop invariant x - y <= 1;
  loop invariant j == y * (y + 1) / 2 + (flag ? y : 0);
  loop invariant i == x * (x + 1) / 2;
  loop invariant i <= j;
  loop invariant i <= j || i + 1 == j;
  loop invariant flag ==> j >= i + x;
  loop invariant flag ==> j - i == y;
  loop invariant 0 <= y;
  loop invariant 0 <= x;
  loop invariant 0 <= j;
  loop invariant 0 <= i;
  loop invariant 0 <= i && 0 <= j;
  loop invariant !flag ==> j >= i;
  loop invariant !flag ==> j - i == 0;
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
  
  while (unknown2()) {
   
    /*@
    loop invariant w >= 1;
    loop invariant z >= 0;
    loop invariant x >= y;
    loop invariant x - y <= 1;
    loop invariant w == z + 1;
    loop invariant z == x + y;
    loop invariant \forall integer k; w % 2 == 1 ==> x >= y;
    loop assigns w, z, x, y;
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