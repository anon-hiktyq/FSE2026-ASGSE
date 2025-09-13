#include <assert.h>
int unknown1();
int unknown2();
int unknown3();
int unknown4();


/*
 * From CAV'12 by Sharma et al.
 */

void main() {
  int x = 0;
  int y = 0;
  int n = 0;
  /*@
  loop invariant x == y;
  loop invariant 0 <= x;
  loop invariant 0 <= y;
  loop assigns x, y;
  
  loop invariant x >= n;
  loop invariant y == x - (x - n);
  loop assigns x, y;
  */
  while(unknown()) {
      x++;
      y++;
  }
  while(x!=n) {
      x--;
      y--;
  }
  // @ assert y==n;
}
