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
  loop invariant i < j;
  loop invariant i + 1 <= j;
  loop invariant i % 2 == 1 ==> j >= 2;
  loop invariant i % 2 == 1 ==> j % 2 == 0;
  loop invariant i % 2 == 1 ==> j % 2 == 0 && j >= 2;
  loop invariant i % 2 == 0 || i % 2 != 0;
  loop invariant i % 2 == 0 ==> j >= 1;
  loop invariant i % 2 == 0 ==> j % 2 == 1;
  loop invariant i % 2 == 0 ==> j % 2 == 1 && j >= 1;
  loop invariant i % 2 != 0 ==> j % 2 != 0 && j > 1;
  loop invariant \forall integer n; n >= 0 ==> j > n;
  loop invariant \forall integer n; n >= 0 ==> i == 2 * n || i == 2 * n + 1;
  loop invariant \forall integer m; m >= 0 ==> j >= m;
  loop invariant \forall integer m; 0 <= m < j ==> m < i || m % 2 == 1;
  loop invariant \exists integer n; i == 2 * n + (flag ? 0 : 1);
  loop invariant \exists integer m; m >= 0 && i == 2 * m || i == 2 * m + 1;
  loop invariant \exists integer k; k >= 0 && i == 2 * k + (flag ? 0 : 1);
  loop invariant 0 <= i && 0 < j;
  loop invariant i / 2 <= j;
  loop invariant i % 2 == 1 ==> j >= 2 && j % 2 == 0;
  loop invariant i % 2 == 0 || j % 2 == 1;
  loop invariant i % 2 == 0 || i % 2 == 1;
  loop invariant i % 2 == 0 ==> j >= 1 && j % 2 == 1;
  loop invariant i % 2 != 0 ==> j % 2 != 0;
  loop invariant \exists integer n; n >= 0 && i == 2 * n + (flag ? 0 : 1);
  loop invariant 1 <= j;
  loop invariant 0 <= j - i;
  loop invariant 0 <= i;
  loop invariant 0 < j;
  loop invariant 0 < flag;
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
  loop invariant b == a * (j - i);
  loop invariant 1 <= j;
  loop invariant 0 <= i;
  loop invariant 0 <= b;
  loop invariant 0 <= a;
  loop invariant 0 < j;
  loop invariant 0 < flag;
  loop assigns b;
  loop assigns a;
  */
  while (unknown2()) {
    a++;
    b += (j - i);
  }
  if (flag) {
    // @ assert a == b;
  }
}