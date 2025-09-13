#include <assert.h>

/*
 * "split.c" from InvGen benchmark suite
 */

void main() {
  int k = 100;
  int b;
  int i;
  int j;
  int n;
  i = j;
  /*@
  loop invariant n <= 2*k;
  loop invariant n <= 2 * k;
  loop invariant i + j == n + 2 * j;
  loop invariant 0 <= n;
  loop invariant (n % 2 == 1) ==> i == j + 1;
  loop invariant (n % 2 == 1) ==> b == 1;
  loop invariant (n % 2 == 1) ==> b == 0;
  loop invariant (n % 2 == 1) ==> (i == j + 1);
  loop invariant (n % 2 == 0) ==> i == j;
  loop invariant (n % 2 == 0) ==> (i == j);
  loop invariant (n % 2 == 0 ==> i == j) && (n % 2 == 1 ==> i == j + 1);
  loop invariant (i - j == 0) || (i - j == 1); // i and j differ by at most 1 during the iterations;
  loop assigns n;
  loop assigns j;
  loop assigns i;
  loop assigns b;
  */
  for( n = 0 ; n < 2*k ; n++ ) {
    if(b) {
      i++;
    } else {
      j++;
    }
    b = !b;
  }
  // @ assert i == j;
}
