#include <stdio.h>

/*@
requires n >= 0;
ensures \result == (\prod integer k; 1 <= k <= n; k);
ensures \result > 0;
assigns \nothing;
*/
int factorial(int n) {

  int i = 1;
  int f = 1;

  /*@
  loop invariant 1 <= i;
  loop invariant 1 <= f;
  loop invariant 0 < f;
  loop assigns i;
  loop assigns f;
  */
  while (i <= n)  {
    f = f * i;
    i = i + 1;
  }
  return f;
}

// write a test
void main() {
  int t = factorial(5);
  // @ assert t == 120;
}