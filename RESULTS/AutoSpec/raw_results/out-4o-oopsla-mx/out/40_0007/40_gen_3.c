#include <assert.h>
int unknown1();
int unknown2();

/*@
requires flag > 0;
*/
void foo(int flag) {
  int i, j, k;
  j = 1;
  if (flag) {
    i = 0;
  } else {
    i = 1;
  }

  /*@
  loop invariant j <= i + 2;
  loop invariant i % 2 != 0 ==> j % 2 != 0;
  loop invariant \forall integer n; 0 <= n <= i ==> (flag > 0);
  loop invariant \exists integer n; n >= 0 && i == (flag ? n * 2 : n * 2 + 1);
  loop invariant 1 <= j;
  loop invariant 0 <= i;
  loop invariant 0 < flag;
  loop invariant (i % 2 != 0) ==> (j % 2 != 0);
  loop assigns j;
  loop assigns i;
  */
  while (unknown1()) {
    i += 2;
    if (i % 2 == 0) {
      j += 2;
    } else j++;
  }

  int a = 0;
  int b = 0;

  /*@
  loop invariant a >= 0;
  loop invariant b == a * (j - i);
  loop invariant 0 <= i;
  loop invariant 1 <= j;
  loop assigns a;
  loop assigns b;
  */
  while (unknown2()) {
    a++;
    b += (j - i);
  }
  if (flag) {
    // @ assert a == b;
  }
}