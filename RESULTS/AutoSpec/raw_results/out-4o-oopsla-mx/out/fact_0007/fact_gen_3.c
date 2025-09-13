#include <stdio.h>

int factorial(int n) {

  int i = 1;
  int f = 1;

  /*@
  loop invariant 1 <= i <= n + 1;
  loop invariant f == \product(k, 1, i-1, k); // f is the product of all integers from 1 to i-1
  loop invariant i >= 1;
  loop assigns i, f;
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