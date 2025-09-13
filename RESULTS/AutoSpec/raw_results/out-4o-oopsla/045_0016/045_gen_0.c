
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
  // For the first loop
  loop invariant x == y;
  loop invariant i >= 0;
  loop invariant j >= 0;
  loop invariant j == i + y * flag;
  loop invariant x >= 0 && y >= 0;
  loop assigns x, y, i, j;
  
  // For the second loop
  loop invariant w >= 1;
  loop invariant z == x + y;
  loop invariant x >= 0 && y >= 0;
  loop assigns x, y, z, w;
  
  // For the innermost loop
  loop invariant w % 2 == 1 ==> x >= y;
  loop invariant z % 2 == 0 ==> y >= x;
  loop assigns x, y;
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