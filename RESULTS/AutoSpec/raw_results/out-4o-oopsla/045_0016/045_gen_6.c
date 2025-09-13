
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
  /* Invariant for the first while loop */
  loop invariant x == y;
  loop invariant i >= 0;
  loop invariant j >= 0;
  loop invariant flag ==> j >= i;
  loop assigns x, y, i, j;
  
  /* Invariant for the second while loop */
  loop invariant w == z + 1;
  loop invariant z >= 0;
  loop invariant x >= y;
  loop invariant x - y <= 1;
  loop assigns x, y, z, w;
  
  /* Invariant for the nested while loop */
  loop invariant x >= y;
  loop invariant x - y <= 1;
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