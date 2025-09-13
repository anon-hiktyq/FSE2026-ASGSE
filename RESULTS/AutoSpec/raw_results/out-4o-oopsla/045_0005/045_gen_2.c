
int unknown1();
int unknown2();
int unknown3();


void foo045(int flag) {
  int x = 0;
  int y = 0;
  int j = 0;
  int i = 0;

 
  /*@
  loop invariant i == x * y;
  loop invariant flag ==> j >= y;
  loop invariant !flag ==> j == y;
  loop invariant x == y;
  loop assigns x, y, i, j;
  
  loop invariant w >= 1;
  loop invariant z == x + y;
  loop invariant w == z + 1;
  loop invariant x == y;
  loop assigns w, z, x, y;
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