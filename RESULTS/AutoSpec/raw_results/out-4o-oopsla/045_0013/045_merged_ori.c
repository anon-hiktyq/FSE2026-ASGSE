
int unknown1();
int unknown2();
int unknown3();


void foo045(int flag) {
  int x = 0;
  int y = 0;
  int j = 0;
  int i = 0;

 
  /*@
  loop invariant z == x + y;
  loop invariant y <= x;
  loop invariant x == y;
  loop invariant x - y <= 1;
  loop invariant w == z + 1;
  loop invariant w % 2 == z % 2;
  loop invariant j >= i || j + 1 >= i;
  loop invariant i >= 0 && j >= 0;
  loop invariant i == j || i == j - 1;
  loop invariant i == j || i + 1 == j;
  loop invariant i == j - flag * x;
  loop invariant i == j - (\exists integer k; 0 <= k < i && flag);
  loop invariant i == j - (\at(flag, Pre) ? x : 0);
  loop invariant flag == 0 || flag == 1;
  loop invariant 1 <= w;
  loop invariant 0 <= y;
  loop invariant 0 <= x;
  loop invariant 0 <= j;
  loop invariant 0 <= i;
  loop invariant (flag ? j >= i : j == i);
  loop invariant (\forall integer k; w % 2 == 1 ==> x == y);
  loop assigns z;
  loop assigns y;
  loop assigns x;
  loop assigns w;
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