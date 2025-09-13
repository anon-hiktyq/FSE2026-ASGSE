#include <assert.h>

int unknown1();
int unknown2();
int unknown3();
int unknown4();

void main() {
  int w = 1, z = 0, x = 0, y = 0;
  while (unknown1()) {
    /*@
    loop invariant z == x + y;
    loop invariant z == x + y || z == 0;
    loop invariant z % 2 == 0;
    loop invariant x >= 0 && y >= 0;
    loop invariant x == y;
    loop invariant w == z + 1;
    loop invariant w == z + 1 || w == 1;
    loop invariant w % 2 == 1;
    loop invariant w % 2 == 1 || z % 2 == 0;
    loop invariant w % 2 == (z + 1) % 2;
    loop invariant 1 <= w;
    loop invariant 0 <= z;
    loop invariant 0 <= y;
    loop invariant 0 <= x;
    loop assigns y;
    loop assigns x;
    ```c;
    ```;
    */
    while (unknown2()) {
      if (w % 2 == 1)
        x++;
      if (z % 2 == 0)
        y++;
    }
    while (unknown4()) {
      z = x + y;
      w = z + 1;
    }
  }
  // @ assert x == y;
}