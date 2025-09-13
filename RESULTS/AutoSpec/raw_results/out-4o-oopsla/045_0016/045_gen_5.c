
int unknown1();
int unknown2();
int unknown3();


void foo045(int flag) {
  int x = 0;
  int y = 0;
  int j = 0;
  int i = 0;

 
  /*@
  ```c
  /*@
  loop invariant x >= 0;
  loop invariant y >= 0;
  loop invariant i >= 0;
  loop invariant j >= 0;
  loop invariant j >= i || flag ==> j == i + (y - x);
  loop invariant j >= i || !flag ==> j == i + (y - x - 1);
  loop assigns x, y, i, j;
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
  
  /*@
  loop invariant w >= 1;
  loop invariant z >= 0;
  loop invariant x >= y;
  loop invariant z == x + y || z == x + y + 1;
  loop assigns x, y, z, w;
  */
  while (unknown2()) {
    /*@
    loop invariant x >= y;
    loop assigns x, y;
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
  ```
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