#include <stdio.h>

int factorial(int n) {

  int i = 1;
  int f = 1;

  /*@
  loop invariant 1 <= i <= n+1;
  loop invariant f == \product(1, i-1, \lambda integer k; k);
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