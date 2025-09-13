#include <stdio.h>

/*@
requires n >= 0;;
requires n >= 0;
ensures n == 0 ==> \result == 1;
ensures \result == \product(1, n, \lambda integer k; k);
ensures \result == \product(1, n, \lambda integer i; i);;
ensures \result == \prod(1, n, \lambda integer k; k);
ensures \result == (\prod integer k; 1 <= k <= n; k);
ensures \result == (\prod integer i; 1 <= i <= n; i);
assigns \nothing;
*/
int factorial(int n) {

  int i = 1;
  int f = 1;

  /*@
  loop invariant 1 <= i;
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