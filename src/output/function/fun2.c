
/*@
axiomatic IterationProperties {
  logic integer iterations(integer i, integer n);
  axiom initial_iteration:
    \forall integer i, n; i > n ==> iterations(i, n) == 0;
  axiom iteration_step:
    \forall integer i, n; i <= n ==> iterations(i, n) == iterations(i + 3, n) + 1;
}
*/

/*@
requires n == \at(n, Pre);
ensures \result == iterations(7, n);
*/
int fun2(int n) {
    int i = 7;
    int x = 1;

    /*@
    loop invariant (7 <= \at(n, Pre)) ==> (i == 7 + 3 * (x - 1));
    loop invariant (!(7 <= \at(n, Pre))) ==> ((x == 1) && (i == 7) && (n == \at(n, Pre)));
    loop invariant n == \at(n, Pre);
    loop assigns i, x;
    loop variant n - i;
    */
    while (i <= n) {
        x += 1;
        i += 3;
    }

    return x;
}
