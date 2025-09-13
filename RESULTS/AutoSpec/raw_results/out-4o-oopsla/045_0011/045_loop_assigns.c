
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
  loop invariant y <= j;
  loop invariant x >= 0 && y >= 0;
  loop invariant x == y;
  loop invariant x <= i;
  loop invariant j >= i || j + 1 >= i;
  loop invariant j == y * (y + 1) / 2 + (flag ? y : 0);
  loop invariant j == i + (flag ? x : 0);
  loop invariant i == x * (x + 1) / 2;
  loop invariant i == j - (flag ? x : 0);
  loop invariant i <= j;
  loop invariant flag ==> j == i + y;
  loop invariant 0 <= y;
  loop invariant 0 <= x;
  loop invariant 0 <= x && 0 <= y;
  loop invariant 0 <= j;
  loop invariant 0 <= i;
  loop invariant 0 <= i && 0 <= j;
  loop invariant 0 <= i && 0 <= j && 0 <= x && 0 <= y;
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
  
  while (unknown2()) {
   
    /*@
    loop assigns w;
    loop assigns y;
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