
/*@
  requires n >= 0;                          // Precondition: n must be non-negative.
  assigns \nothing;                         // Function does not modify global state.
  ensures n < 7 ==> \result == 1;           // Postcondition: If n < 7, x remains 1.
  ensures n >= 7 ==> \result == (n - 7) / 3 + 1; // Postcondition: If n >= 7, x follows the arithmetic progression formula.
*/
int fun24(int n) {
    int i = 7;
    int x = 1;

    /*@
      loop invariant (7 <= \at(n,Pre)) ==> (i == 7 + 3 * (x - 1)); // Relation between i and x when n >= 7.
      loop invariant (7 <= \at(n,Pre)) ==> (x == (i - 7) / 3 + 1); // Relation between x and i when n >= 7.
      loop invariant !(7 <= \at(n,Pre)) ==> ((x == 1) && (i == 7) && (n == \at(n,Pre))); // When n < 7, x and i remain unchanged.
      loop invariant n == \at(n,Pre);                 // n remains constant throughout the loop.
      loop assigns x, i;                              // Loop modifies x and i.
      loop variant n - i;                             // Loop variant ensures termination.
    */
    while (i <= n) {
        x += 1;
        i += 3;
    }

    return x;
}
