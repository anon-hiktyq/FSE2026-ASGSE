


/*@
axiomatic Factorial {
    logic integer factorial(integer k);
    axiom factorial_base:
        factorial(0) == 1;
    axiom factorial_step:
        \forall integer k; k > 0 ==> factorial(k) == k * factorial(k - 1);
}
*/

/*@
requires n >= 0;
ensures \result == factorial(n);
*/
int factorial9(int n) {

  int i = 1;
  int f = 1;

  /*@
    loop invariant (1 <= \at(n,Pre)) ==> (1 <= i <= n + 1);
    loop invariant (1 <= \at(n,Pre)) ==> (f == factorial(i - 1));
    loop invariant (!(1 <= \at(n,Pre))) ==> ((f == 1)&&(i == 1)&&(n == \at(n,Pre)));
    loop invariant n == \at(n,Pre);
    loop assigns i, f;
    loop variant n - i;
  */
  while (i <= n)  {
    f = f * i;
    i = i + 1;
  }
            
  return f;
}

void goo9() {
  int t = factorial9(5);
   //@ assert t == 120;
 
}
