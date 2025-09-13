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
  loop invariant 0 <= n <= 2 * k;
  loop invariant i + j == 2 * k;
  loop invariant i - j == 0;
  loop invariant b == (\at(b, Pre) ^ (n % 2 == 1));
  loop assigns n, i, j, b;
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
