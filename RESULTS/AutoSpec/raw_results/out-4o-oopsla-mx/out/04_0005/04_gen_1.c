#include <assert.h>
int unknown1();
int unknown2();
int unknown3();
int unknown4();

/*
 * Taken from Gulwani PLDI'08:
 * Program Analysis as Constraint Solving
 */

void main() {
  int x, y;

  x = -50;
  /*@
  loop invariant x <= -50 + y * (y - 1) / 2;
  loop invariant x < 0;
  loop invariant 0 <= y;
  loop assigns x;
  loop assigns y;
  loop invariant \forall integer n; 0 <= n < y ==> x + y - n - 1 < 0;
  */
  while( x < 0 ) {
	x = x + y;
	y++;
  }
  // @ assert y > 0;
}

