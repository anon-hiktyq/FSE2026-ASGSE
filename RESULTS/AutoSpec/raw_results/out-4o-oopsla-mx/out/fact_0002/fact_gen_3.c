#include <stdio.h>

/*@
requires n >= 0;
ensures \result == (\prod integer i; 1 <= i <= n; i);
ensures n == 0 ==> \result == 1;
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