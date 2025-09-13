#include <assert.h>
int unknown1();

/*
 * "nest-if8" from InvGen benchmark suite
 */

void main() {
  int i, j, k, n, m;
  if (m + 1 < n);
  else return;
  for (i = 0; i < n; i += 4) {
    /*@
    loop invariant 0 <= i <= n;
    loop invariant 0 <= j <= m;
    loop invariant \forall integer x; 0 <= x < j ==> x >= i;
    loop invariant \forall integer t; 0 <= t < j ==> t >= i;
    loop invariant \forall integer p; 0 <= p < j ==> p >= i;
    loop invariant \forall integer l; 0 <= l < j ==> l >= i;
    loop invariant \forall integer k; 0 <= k < j ==> k >= i;
    loop invariant \forall integer x; 0 <= x < j ==> x >= 0;
    loop assigns j;
    loop assigns i;
    loop assigns k;
    */
    for (j = i; j < m;) {
      if (unknown1()) {
        // @ assert j >= 0;
        j++;
        k = 0;
        /*@
        loop invariant k <= j;
        loop invariant \forall integer x; 0 <= x < k ==> x < j;
        loop invariant \forall integer t; 0 <= t < k ==> t < j;
        loop invariant \forall integer p; 0 <= p < k ==> p < j;
        loop invariant \forall integer l; 0 <= l < k ==> l < j;
        loop invariant 0 <= k;
        loop invariant 0 <= j;
        loop assigns k;
        */
        while (k < j) {
          k++;
        }
      } else {
        // @ assert n + j + 5 > i;
        j += 2;
      }
    }
  }
}