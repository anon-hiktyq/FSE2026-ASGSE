#include <assert.h>

int unknown1();
int unknown2();
int unknown3();
int unknown4();

void foo(int flag) {
  int x = 0;
  int y = 0;
  int j = 0;
  int i = 0;

  /*@
  loop invariant z == x + y;
  loop invariant z < w;
  loop invariant z % 2 == 0 ==> w % 2 == 1;
  loop invariant y <= x;
  loop invariant x == y;
  loop invariant w == z + 1;
  loop invariant w % 2 == z % 2;
  loop invariant w % 2 == 1 || z % 2 == 0;
  loop invariant w % 2 == 1 ==> z % 2 == 0;
  loop invariant i == j - flag * (j - i);
  loop invariant i == j - (flag ? y : 0);
  loop invariant i == j - (flag ? x : 0);
  loop invariant i == j - (flag ? (\count) : 0);
  loop invariant i == j - (\exists integer k; 0 <= k < i && flag ==> j + 1);
  loop invariant i == j - (\at(j,Pre) - \at(i,Pre));
  loop invariant i <= j;
  loop invariant flag ==> j >= i;
  loop invariant flag ==> j == i + x;
  loop invariant \forall integer k; k < w ==> (k % 2 == 1 ? (x >= y) : true);
  loop invariant 1 <= w;
  loop invariant 0 <= z;
  loop invariant 0 <= y;
  loop invariant 0 <= j;
  loop invariant 0 <= i;
  loop invariant (flag ==> j >= i) || (!flag ==> j >= i - 1);
  loop invariant !flag ==> j >= i - x;
  loop invariant !flag ==> j == i;
  loop assigns z;
  loop assigns y;
  loop assigns x;
  loop assigns w;
  loop assigns j;
  loop assigns i;
  /* Loop invariant for the second while loop */;
  /* Loop invariant for the first while loop */;
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