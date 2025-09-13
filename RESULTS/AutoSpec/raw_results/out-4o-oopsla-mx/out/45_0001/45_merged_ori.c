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
  loop invariant z == x + y;;
  loop invariant z == x + y;
  loop invariant y <= x;
  loop invariant x == y;;
  loop invariant x == y;
  loop invariant x <= j;
  loop invariant x - y == w - z;
  loop invariant w == z + 1;;
  loop invariant w == z + 1;
  loop invariant w % 2 == z % 2;;
  loop invariant w % 2 == z % 2;
  loop invariant w % 2 == (z % 2 == 0 ? 1 : 0);
  loop invariant j >= i || j < i;
  loop invariant j == y * (y + 1) / 2 + (flag ? y : 0);;
  loop invariant j == i + (\exists integer k; 0 <= k < i && flag ==> 1);
  loop invariant i == x * (x + 1) / 2;;
  loop invariant i == j || i == j - 1;
  loop invariant i == j || i < j;;
  loop invariant i == j || i + 1 == j;
  loop invariant i == j - (flag ? x : 0);
  loop invariant i <= j;
  loop invariant \forall integer k; 0 <= k < y ==> (!flag ==> j == i + y);
  loop invariant \forall integer k; 0 <= k < x ==> (flag ==> j == i + x + 1);
  loop invariant 1 <= w;
  loop invariant 0 <= z;
  loop invariant 0 <= j;
  loop invariant 0 <= i;
  loop invariant 0 < w;
  loop invariant (z % 2 == 0 ==> y >= x);
  loop invariant (w % 2 == 1 ==> x >= y);
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