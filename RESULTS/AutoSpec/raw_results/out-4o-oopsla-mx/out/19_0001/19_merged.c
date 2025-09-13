#include <assert.h>
int unknown1();
int unknown2();
int unknown3();
int unknown4();

/*
 * From "Simplifying Loop Invariant Generation using Splitter Predicates", Sharma et al. CAV'11
 */

/*@
requires n >= 0;
requires m >= 0;
requires m < n;
*/
void foo(int n, int m)
{
  int x = 0; 
  int y = m;
  /*@
  loop invariant y == m + (x > m ? x - m : 0);
  loop invariant y == (x > m ? m + (x - m) : m);
  loop invariant y <= n;
  loop invariant x <= y;
  loop invariant x <= n;
  loop invariant m <= y;
  loop invariant 0 <= x;
  loop invariant 0 <= n;
  loop invariant 0 <= m;
  loop invariant (x > m ==> y == m + (x - m));
  loop invariant (x <= m ==> y == m);
  loop assigns y;
  loop assigns x;
  */
  while(x < n) {
    x++;
    if(x > m) y++;
  }
  //@ assert y==n;
}
