
/*@
axiomatic SumEvenNumbers {
    logic integer sum_even(integer start, integer end);
    axiom empty:
        \forall integer s, e; s >= e ==> sum_even(s, e) == 0;
    axiom range:
        \forall integer s, e; s < e ==> sum_even(s, e) == sum_even(s, e-1) + 2*(e-1);
}
*/

/*@
requires n >= 0;
ensures \result == sum_even(0, n/2 + 1);
*/
int func11(int n) {
    int sum = 0;
    int i = 0;

    /*@
      loop invariant (0 <= \at(n,Pre)/2) ==> (0 <= i <= n/2 + 1);
      loop invariant (!(0 <= \at(n,Pre)/2)) ==> ((i == 0)&&(sum == 0)&&(n == \at(n,Pre)));
      loop invariant n == \at(n,Pre);
    */
    while (i <= n/2) {
        sum = sum + 2*(i);
        i++;
    }

    return sum;
}
