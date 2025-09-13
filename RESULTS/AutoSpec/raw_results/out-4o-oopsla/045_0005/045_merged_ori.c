
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
  loop invariant x == y || x + 1 == y;
  loop invariant w == z + 1;
  loop invariant w % 2 == z % 2;
  loop invariant w % 2 == 1 || w % 2 == 0;
  loop invariant j >= i || j == i - x;
  loop invariant j == i + (flag ? x : 0);
  loop invariant i == x * y;
  loop invariant i == j || i + 1 == j;
  loop invariant i == j - (\if flag then 1 else 0)*(\count{unknown1});
  loop invariant i == j - (\exists integer k; 0 <= k <= x && (flag ? k : 0));
  loop invariant i == j - (\exists integer k; 0 <= k <= flag);;
  loop invariant i <= j;
  loop invariant flag ==> j >= y;
  loop invariant flag ==> j == i + x;
  loop invariant 1 <= w;
  loop invariant 0 <= z;
  loop invariant 0 <= y;
  loop invariant 0 <= x;
  loop invariant 0 <= j;
  loop invariant 0 <= i;
  loop invariant !flag ==> j == y;
  loop invariant !flag ==> j == i;
  loop assigns z;
  loop assigns y;
  loop assigns x;
  loop assigns w;
  loop assigns j;
  loop assigns i;
  ```c;
  ```;
  Second `while` loop:;
  First `while` loop:;
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