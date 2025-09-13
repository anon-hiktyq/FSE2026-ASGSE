
/*@
  requires n >= 0; // Precondition: Input must be a non-negative integer
  ensures \result == (n == 0 ? 1 : n * \result); // Postcondition: Result is the factorial of n
*/
int factorial9(int n) {

  int i = 1;
  int f = 1;

  /*@
    loop invariant (1 <= \at(n,Pre)) ==> (1 <= i <= n + 1); // i is within the valid range during the loop
    loop invariant (!(1 <= \at(n,Pre))) ==> ((f == 1) && (i == 1) && (n == \at(n,Pre))); // If n < 1, loop does not execute
    loop invariant n == \at(n,Pre); // n remains unchanged throughout the loop
    loop invariant f == (\prod (1 <= j < i)); // f holds the partial factorial up to i-1
    loop assigns f, i; // Variables modified in the loop
    loop variant n - i + 1; // Decreasing variant to ensure loop termination
  */
  while (i <= n) {
    f = f * i;
    i = i + 1;
  }

  return f;
}

void goo9() {
  int t = factorial9(5);
  //@ assert t == 120;
}
