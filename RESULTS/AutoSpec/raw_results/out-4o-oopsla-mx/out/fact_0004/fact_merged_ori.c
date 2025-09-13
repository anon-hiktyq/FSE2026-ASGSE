#include <stdio.h>

/*@
requires n >= 0;
ensures n == 0 ==> \result == 1;
ensures \result > 0;
ensures \result == \product(1..n, \lambda integer x; x);
ensures \result == \prod(1, n, i -> i); // Product from 1 to n;
ensures \result == \prod(1, n, \lambda integer i; i);
ensures \result == 1 ==> n == 0 || n == 1;
ensures \result == (\product(integer k; 1 <= k <= n; k));
ensures \result == (\product integer i; 1 <= i <= n; i);
ensures \result == (\prod integer k; 1 <= k <= n; k);
ensures \result == (\prod integer i; 1 <= i <= n; i);
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