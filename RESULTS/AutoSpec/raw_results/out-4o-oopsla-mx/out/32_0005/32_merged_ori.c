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
  loop invariant i - j == n - k;
  loop invariant i - j == n - 2 * (n / 2);
  loop invariant i - j == 2 * (n / 2) - n % 2;
  loop invariant i - j == 0;
  loop invariant i + j == 2*j + n;
  loop invariant i + j == 2 * k;
  loop invariant i + j == 2 * j_0 + n; // j_0 is the initial value of j;
  loop invariant i + j == 2 * j_0 + n;
  loop invariant b == (\at(b, Pre) ^ (n % 2 == 1));
  loop invariant 0 <= n;
  loop invariant (n % 2 == 1) ==> (i == j + 1);
  loop invariant (n % 2 == 0) ==> (i == j);
  loop invariant (n % 2 == 0) ==> (b == \false);
  loop invariant (n % 2 == 0 && i == j) || (n % 2 == 1 && (i == j + 1 || j == i + 1));
  loop invariant (n % 2 == 0 && b == 0) || (n % 2 == 1 && b == 1);
  loop invariant (n % 2 != 0) ==> (b == \true);
  loop invariant (b == 0 && i == j + 1) || (b == 1 && i == j);
  loop invariant (b && n % 2 == 0) || (!b && n % 2 == 1);
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
