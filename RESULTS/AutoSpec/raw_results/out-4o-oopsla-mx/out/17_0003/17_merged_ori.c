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
  loop invariant m < i, m*(m+1)/2);
  loop invariant k == 1 + \sum(1 <= m < i, \sum(0 <= l < m, m-l));
  loop invariant k == 1 + \sum integer m; 1 <= m < i; m * (m + 1) / 2;
  loop invariant k == 1 + \sum integer m; 1 <= m < i; \sum integer l; 0 <= l < m; (m - l);
  loop invariant k == (i*(i+1))/2;
  loop invariant k == (i * (i + 1)) / 2;
  loop invariant j == i;
  loop invariant j <= i;
  loop invariant i <= n;
  loop invariant i <= k;
  loop invariant 1; <= i;
  loop invariant 1 <= k;
  loop invariant 1 + \sum(1 <= m;
  loop invariant 1 + \sum(1 <= k;
  loop invariant 1 + (i * (i - 1))/2 <= k;
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
