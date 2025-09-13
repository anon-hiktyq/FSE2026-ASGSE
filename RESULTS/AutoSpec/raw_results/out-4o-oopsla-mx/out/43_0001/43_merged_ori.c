#include <assert.h>
int unknown1();
int unknown2();
int unknown3();
int unknown4();

/*
 * Based on ex16 from NECLA Static Analysis Benchmarks
 */

int foo(int x, int y)
{
  int i=0;
  int t=y;
   
  if (x==y) return x;
  
  /*@
  loop invariant x >= 0 ==> y >= t;
  loop invariant x > 0 ==> y >= t;
  loop invariant x > 0 ==> y >= t + x * i;
  loop invariant x > 0 ==> y >= t + i * x;
  loop invariant x == y || y > x;
  loop invariant x == y || x != y;
  loop invariant x == t || x > t || x < t;
  loop invariant x == t || x > 0;
  loop invariant x == t || x != t;
  loop invariant x <= 0 ==> y == t;
  loop invariant t <= y;
  loop invariant t <= \forall integer k; y;
  loop invariant \forall integer k; 0 <= k <= i ==> y >= t;
  loop invariant 0 <= i;
  loop assigns y;
  loop assigns i;
  */
  while (unknown1()){
    if (x > 0)   
      y = y + x;
  }
   
  // @ assert y >= t;
  return 0;
}


