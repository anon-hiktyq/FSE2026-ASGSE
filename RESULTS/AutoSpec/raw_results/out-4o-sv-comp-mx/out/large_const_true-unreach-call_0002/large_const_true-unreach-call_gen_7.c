#include "assert.h"

/*@
requires 0 <= n && n < 2;
requires 0 <= v;
*/
int foo(int n, int v) {
  int c1 = 4000;
  int c2 = 2000;
  int c3 = 10000;
  //int n, v;
  int i, k, j;


  k = 0;
  i = 0;
  /*@
  loop invariant k == i * (v == 0 ? c1 : (v == 1 ? c2 : c3));
  loop invariant k == (i * (v == 0 ? c1 : (v == 1 ? c2 : c3)));
  loop invariant i <= n;
  loop invariant 0 <= i;
  loop assigns k;
  loop assigns i;
  */
  while( i < n ) {
    i++;
    if( v == 0 )
      k += c1;
    else if( v == 1 )
      k += c2;
    else
      k += c3;
  }

  j = 0;
  /*@
  ```c
  /*@
  loop invariant 0 <= j <= n;
  loop invariant k == (n - j) * (v == 0 ? c1 : (v == 1 ? c2 : c3));
  loop invariant k >= 0;
  loop assigns j;
  loop assigns k;
  */
  ```
  */
  while( j < n ) {
    // @ assert k > 0;
    j++;
    k--;
  }

  return 0;
}