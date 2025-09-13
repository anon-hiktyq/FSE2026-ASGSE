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
    loop invariant i % 4 == 0;
    loop invariant \forall integer x; 0 <= x < i ==> x % 4 == 0;
    loop invariant \forall integer p; 0 <= p < j ==> p < n;
    loop assigns i, j, k;
    */
    for (j = i; j < m;) {
      if (unknown1()) {
        // @ assert j >= 0;
        j++;
        k = 0;
        /*@
        loop invariant k <= m;
        loop invariant k <= j;
        loop invariant \forall integer x; 0 <= x < k ==> x < j;
        loop invariant \forall integer p; 0 <= p < k ==> p < j;
        loop invariant 0 <= k;
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