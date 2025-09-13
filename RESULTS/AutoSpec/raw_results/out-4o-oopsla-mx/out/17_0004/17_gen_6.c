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
  loop invariant k >= i;
  loop invariant 0 <= j <= i;
  loop invariant \forall integer m; 1 <= m <= i ==> \forall integer l; 0 <= l < m ==> k >= m-l;
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
