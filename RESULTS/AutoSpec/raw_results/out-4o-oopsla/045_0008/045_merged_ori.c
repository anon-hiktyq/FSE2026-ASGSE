
int unknown1();
int unknown2();
int unknown3();


void foo045(int flag) {
  int x = 0;
  int y = 0;
  int j = 0;
  int i = 0;

 
  /*@
  loop invariant z == x + y;;
  loop invariant z <= w;;
  loop invariant z <= w;
  loop invariant z < w;
  loop invariant z + 1 <= w;
  loop invariant z % 2 == w % 2;
  loop invariant z % 2 == 1 || x >= y;
  loop invariant z % 2 == 1 || w % 2 == 0;
  loop invariant z % 2 == 1 ==> w % 2 == 0;
  loop invariant z % 2 == 0;;
  loop invariant z % 2 == 0 || x <= y + 1;
  loop invariant z % 2 == 0 || x != y;
  loop invariant z % 2 == 0 || w % 2 == 1;;
  loop invariant z % 2 == 0 ==> x >= y;
  loop invariant z % 2 == 0 ==> w % 2 == 1;
  loop invariant y; <= x;
  loop invariant y <= z;
  loop invariant x >= 0 && y >= 0;;
  loop invariant x == y || x == y + 1;;
  loop invariant x == y || x == y + 1;
  loop invariant x + y == z;
  loop invariant x + y == w - 1;;
  loop invariant x + y <= z;
  loop invariant x % 2 == w % 2;
  loop invariant w == z + 1;;
  loop invariant w == z + 1;
  loop invariant w == x + y + 1;;
  loop invariant w == x + y + 1;
  loop invariant w % 2 == 1 ==> x > y;
  loop invariant \forall integer k; k % 2 == 1 ==> w > z;;
  loop invariant \forall integer k; 0 <= k <= z ==> (w + k) % 2 == 1;
  loop invariant \forall integer k; 0 <= k <= w ==> k + y <= x + z;
  loop invariant \forall integer k; 0 <= k < i ==> (flag || j >= i);;
  loop invariant 1 <= w;;
  loop invariant 1 <= w;
  loop invariant 0 <= z;;
  loop invariant 0 <= z;
  loop invariant 0 <= z && 1 <= w;;
  loop invariant 0 <= y;;
  loop invariant 0 <= x;;
  loop invariant 0 <= w;
  ```c;
  ```;
  loop invariant y <= x;
  loop invariant x == y;
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