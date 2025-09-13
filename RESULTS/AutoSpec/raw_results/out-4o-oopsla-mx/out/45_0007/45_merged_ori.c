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
  loop invariant z % 2 == 0 ==> y++;
  loop invariant y == x;
  loop invariant x >= 0 && y >= 0;
  loop invariant x == y;
  loop invariant x + y <= z;
  loop invariant w >= 1 && z >= 0;
  loop invariant w == z + 1;
  loop invariant w % 2 == z % 2;
  loop invariant i == j || i + 1 == j;
  loop invariant i == j || i + 1 == j || (flag && i == j - 1);
  loop invariant i == j - flag * \sum_{k=1}^{x} 1;
  loop invariant i == j - (flag ? y : 0);
  loop invariant i == j - (\sum_{k=0}^{x-1} (flag ? 1 : 0));
  loop invariant i == j - (\sum integer k; 0 <= k < y && flag ==> k + 1);
  loop invariant i <= j;
  loop invariant \forall integer k; w == z + 1;
  loop invariant \forall integer k; w %2 == 1 ==> x++;
  loop invariant \forall integer k; i <= k < n-1 ==> a[k] <= a[k+1];
  loop invariant \forall integer k; 0 <= k ==> x >= k && y >= k;
  loop invariant 1 <= w;
  loop invariant 0 <= y;
  loop invariant 0 <= x;
  loop invariant 0 <= j;
  loop invariant 0 <= i;
  loop invariant 0 < w;
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