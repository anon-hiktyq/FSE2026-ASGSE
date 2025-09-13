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
  loop invariant k == \sum(1 <= u < i, \sum(0 <= v < u, u - v)) + 1;
  loop invariant k == \sum(1 <= t < i, \sum(0 <= s < t, (t - s))) + 1;
  loop invariant k == 1 + \sum(1 <= p < i, \sum(0 <= q < p, p-q));
  loop invariant k == 1 + \sum(1 <= p < i, \sum(0 <= q < p, p - q));
  loop invariant k == 1 + \sum(1 <= m < i, \sum(0 <= p < m, (m - p)));
  loop invariant k == 1 + \sum(1 <= m < i, \sum(0 <= p < m, (m - p))) + \sum(0 <= q < j, (i - q));
  loop invariant j <= i;
  loop invariant i <= n;
  loop invariant i <= k;
  loop invariant \forall integer p, q; 1 <= p < i && 0 <= q < p ==> k >= (p - q);
  loop invariant 1 <= k;
  loop invariant 1 + (i * (i - 1)) / 2 <= k;
  loop invariant 0 <= j;
  loop invariant 0 <= i;
  loop assigns k;
  loop assigns j;
  */
  while(j < i) {
      k += (i-j);
      j++;
  }
  i++;
 }
 // @ assert k >= n;
 
}
