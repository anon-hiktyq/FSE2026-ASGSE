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
  loop invariant k == \sum{0 <= m < i, 0 <= p < m} (m - p) + i;
  loop invariant k == \sum{0 <= a < j}(i-a) + 1;
  loop invariant k == \sum(1 <= p < i, \sum (0 <= q < p, (p - q))) + i;
  loop invariant j == 0;
  loop invariant j <= i;
  loop invariant i <= n;
  loop invariant i <= k;
  loop invariant i - j <= k;
  loop invariant i - j + 1 <= k;
  loop invariant \forall integer m; 1 <= m <= i ==> \forall integer l; 0 <= l < m ==> k >= m-l;
  loop invariant \forall integer m; 0 <= m < j ==> k >= (i - m);
  loop invariant \forall integer m; 0 <= m < j ==> k == k + (i - m - 1);
  loop invariant \forall integer m; 0 <= m < i ==> k >= m + 1;
  loop invariant 1 <= k;
  loop invariant 1 <= k - (i*(i-1))/2;
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
