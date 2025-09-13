#include <stdio.h>

int factorial(int n) {

  int i = 1;
  int f = 1;

  /*@
  loop invariant i > n || f == n!;
  loop invariant i <= n+1;
  loop invariant i <= n + 1;
  loop invariant f == \product(integer k; 1 <= k < i; k);
  loop invariant f == \product(integer k = 1, i - 1, k);
  loop invariant f == \product(1, i-1, \lambda integer k; k);
  loop invariant f == (\product integer k; 1 <= k < i; k);
  loop invariant \forall integer k; 1 <= k < i ==> f == \product(1, k, \lambda integer j; j);
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