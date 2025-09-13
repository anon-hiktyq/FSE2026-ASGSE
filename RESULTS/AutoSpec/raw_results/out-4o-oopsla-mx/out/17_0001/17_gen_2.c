#include <assert.h>
int unknown1();
int unknown2();
int unknown3();
int unknown4();

void foo(int n)
{
 int k=1;
 int i=1;
 int j=0;
 while(i < n) {
  j = 0;
  /*@
  loop invariant 0 <= i <= n;
  loop invariant k == 1 + \sum(1 <= m < i, \sum(0 <= p < m, (m - p)));
  loop invariant 0 <= j <= i;
  loop invariant k == 1 + \sum(1 <= m < i, \sum(0 <= p < m, (m - p))) + \sum(0 <= q < j, (i - q));
  loop assigns i, j, k;
  */
  while(j < i) {
      k += (i-j);
      j++;
  }
  i++;
 }
 // @ assert k >= n;
 
}
