#include <limits.h>
#include "assert.h"

/*@
requires INT_MIN < n0 && n0 < INT_MAX;
requires INT_MIN < n1 && n1 < INT_MAX;
*/
void foon(int n0, int n1) {
  //int n0, n1;
  int i0 = 0;
  int k = 0;


  /*@
  loop invariant n0 - i0 == k;
  loop invariant k == n0 + n1 - j1;
  loop invariant k == n0 + i1 - 1;
  loop invariant k == i0 + i1;
  loop invariant k == (n0 + n1) - j1;
  loop invariant k <= n0;
  loop invariant j1 <= n0 + n1;
  loop invariant i1 <= n1;
  loop invariant i1 <= k;
  loop invariant i0 <= n0;
  loop invariant \forall integer r; 0 <= r < j1 ==> k == (n0 + n1) - r;
  loop invariant \forall integer q; 0 <= q < i1 ==> k == i0 + q;
  loop invariant \forall integer p; 0 <= p < i0 ==> k == p;
  loop invariant \forall integer m; 0 <= m < i0 ==> k == m;
  loop invariant \forall integer j; 0 <= j < i0 ==> k == j + 1;
  loop invariant 0 <= k;
  loop invariant k == i0;
  loop invariant 0 <= i0;
  loop assigns k;
  loop assigns i0;
  */
  while( i0 < n0 ) {
    i0++;
    k++;
  }

  int i1 = 0;
  /*@
  loop invariant k == i0 + i1;
  loop invariant i1 <= k;
  loop invariant 0 <= i1;
  loop assigns k;
  loop assigns i1;
  */
  while( i1 < n1 ) {
    i1++;
    k++;
  }

  int j1 = 0;
  /*@
  loop invariant 0 <= j1;
  loop assigns k;
  loop assigns j1;
  */
  while( j1 < n0 + n1 ) {
      // @ assert k > 0;
      j1++;
      k--;
  }
}