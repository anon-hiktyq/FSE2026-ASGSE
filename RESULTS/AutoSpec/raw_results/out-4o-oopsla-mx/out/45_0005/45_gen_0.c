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
  loop invariant x == y;
  loop invariant i == x * (x + 1) / 2;
  loop invariant j == y * (y + 1) / 2 + (flag ? y : 0);
  loop invariant x >= 0;
  loop invariant y >= 0;
  loop assigns x, y, i, j;
  
  loop invariant w >= 1;
  loop invariant z == x + y || z % 2 == 0;
  loop invariant (w % 2 == 1) ==> x >= y;
  loop invariant (w % 2 == 0) ==> y >= x - 1;
  loop assigns x, y, z, w;
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