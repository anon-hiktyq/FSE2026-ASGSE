#include <stdio.h>

int factorial(int n) {

  int i = 1;
  int f = 1;

  /*@
  loop invariant i <= n+1;
  loop invariant i <= n + 1;
  loop invariant f == \product(k, 1, i - 1, k); // f is the product of all integers from 1 to i-1;
  loop invariant f == \product(integer k; 1 <= k < i; k);
  loop invariant f == \product(1, i-1, \lambda integer k; k);
  loop invariant f == \product(1, i - 1, \lambda integer k; k); // f is the product of integers from 1 to i-1;
  loop invariant f == \prod(1..i-1, \lambda int k; k);
  loop invariant f == \prod(1, i - 1, \lambda integer k; k); // f is the product of all integers from 1 to i-1;
  loop invariant f == (\prod integer k; 1 <= k < i; k);
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