#include <assert.h>

int unknown1();
int unknown2();
int unknown3();
int unknown4();

int main() {

  int w = 1;
  int z = 0;
  int x = 0;
  int y = 0;

  /*@
  loop invariant z % 2 == y % 2;
  loop invariant z % 2 == 0 || z % 2 == 1;
  loop invariant z % 2 == 0 ==> y == z / 2;
  loop invariant y <= z;
  loop invariant y <= z + 1;
  loop invariant x >= 0 && y >= 0;
  loop invariant x <= y;
  loop invariant x <= w;
  loop invariant x <= w - 1;
  loop invariant x <= 1;
  loop invariant w % 2 == 1 || w % 2 == 0;
  loop invariant w % 2 == 1 ==> x == w - 1;
  loop invariant w % 2 == 0 || w % 2 == 1;
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
    if (w % 2 == 1) {
      x++;
      w++;
    }
    if (z % 2 == 0) {
      y++;
      z++;
    }
  }

  //@ assert x <= 1;
  return 0;
}