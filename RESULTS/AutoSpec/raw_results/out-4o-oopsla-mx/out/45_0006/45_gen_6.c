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
  loop invariant y <= x;
  loop invariant y * (y - 1) / 2 <= j;
  loop invariant x == y;
  loop invariant x == y || x == y + 1;
  loop invariant x * (x - 1) / 2 <= i;
  loop invariant j == y * (y + 1) / 2 || j == y * (y + 1) / 2 + y;
  loop invariant j == y * (y + 1) / 2 + (flag ? y : 0);
  loop invariant j == y * (y + 1) / 2 + (flag ? x : 0);
  loop invariant i >= 0 && j >= 0;
  loop invariant i == x * (x + 1) / 2;
  loop invariant i <= j;
  loop invariant flag ==> j >= i;
  loop invariant 0 <= y;
  loop invariant 0 <= x;
  loop invariant 0 <= x == y;
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
  while (unknown2()) {
    /*@
    loop invariant x == y || x == y + 1;
    loop invariant w % 2 == 1 || z % 2 == 0;
    loop invariant z == x + y || z == x + y + 1;
    loop invariant w == z + 1;
    loop invariant x >= y;
    loop invariant x >= 0 && y >= 0 && z >= 0 && w >= 0;
    loop assigns x, y, w, z;
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