
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
  /* Loop invariants for the first while loop */
  loop invariant x == y;
  loop invariant i >= 0 && j >= 0;
  loop invariant i == x * (x + 1) / 2; // Sum of first 'x' integers
  loop invariant j == y * (y + 1) / 2 + (flag ? y : 0); // Adjusted sum based on flag
  loop assigns x, y, i, j;
  
  /* Loop invariants for the second while loop */
  loop invariant w >= 1;
  loop invariant z == x + y;
  loop invariant x >= y;
  loop invariant x - y <= 1; // Ensures x and y remain equal or differ by at most 1
  loop assigns x, y, z, w;
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