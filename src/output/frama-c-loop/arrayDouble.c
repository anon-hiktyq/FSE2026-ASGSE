
/*@
  requires a != \null; // Pointer validation: input array must not be NULL
  requires n > 0;      // Precondition: array size must be positive
  requires \valid(a + (0 .. n-1)); // Precondition: the array must be valid for the given range
  ensures \forall integer i; 0 <= i < n ==> a[i] == \at(a[i], Pre) * 2; // Postcondition: all elements are doubled
  ensures n == \at(n, Pre); // Postcondition: size of the array remains unchanged
  ensures a == \at(a, Pre); // Postcondition: pointer remains unchanged
*/
void arrayDouble(int *a, unsigned int n) {
    int p = 0;

    /*@
      loop invariant 0 <= p <= n; // Loop invariant: loop counter is within bounds
      loop invariant \forall integer i; 0 <= i < p ==> a[i] == \at(a[i], Pre) * 2; // Loop invariant: all processed elements are doubled
      loop invariant \forall integer i; p <= i < n ==> a[i] == \at(a[i], Pre); // Loop invariant: unprocessed elements remain unchanged
      loop assigns p, a[0..n-1]; // Loop assigns clause: specifies variables modified in the loop
      loop variant n - p; // Loop variant: ensures loop termination
    */
    while (p < n) {
        a[p] = a[p] * 2;
        p = p + 1;
    }
}
