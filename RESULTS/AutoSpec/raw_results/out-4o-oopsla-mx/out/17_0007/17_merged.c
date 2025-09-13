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
  loop invariant j <= i;
  loop invariant i <= n;
  loop invariant i <= k;
  loop invariant \forall integer m; 0 <= m < j ==> k >= (i * (i - 1)) / 2 + (j * (j - 1)) / 2;
  loop invariant \forall integer m; 0 <= m < i ==> k >= n;
  loop invariant \forall integer m; 0 <= m < i ==> k >= (i * (i - 1)) / 2 + 1;
  loop invariant \forall integer m; 0 <= m < i ==> k >= (1 + (i * (i - 1)) / 2);
  loop invariant 1 <= k;
  loop invariant 1 + (i * (i - 1)) / 2 <= k;
  loop invariant 0 <= j;
  loop invariant 0 <= i;
  loop invariant (i * (i - 1)) / 2 <= k;
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
