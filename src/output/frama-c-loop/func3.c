
/*@
  requires \valid(a + (0 .. n-1));        // Array 'a' must be valid for 'n' elements.
  requires \valid(sum);                  // Pointer 'sum' must be valid.
  requires n >= 0;                       // Size of the array must be non-negative.
  assigns *sum;                          // 'sum' is modified by the function.
  ensures *sum == \sum_{i=0}^{n-1} (a[i] == x ? x : 0);  // Postcondition for the sum.
  ensures \result == \sum_{i=0}^{n-1} (a[i] == x ? 1 : 0); // Postcondition for the count.
*/
int func3(int *a, int n, int x, int *sum) {
    int p = 0;
    int count = 0;
    *sum = 0;

    /*@
      loop invariant 0 <= p && p <= n;                              // 'p' is within bounds.
      loop invariant count == \sum_{i=0}^{p-1} (a[i] == x ? 1 : 0); // Count reflects occurrences of 'x' up to 'p'.
      loop invariant *sum == count * x;                             // Sum reflects occurrences of 'x' up to 'p'.
      loop assigns p, count, *sum;                                  // Variables modified in the loop.
      loop variant n - p;                                           // Loop progresses toward termination.
    */
    while (p < n) {
        if (a[p] == x) {
            count = count + 1;
            *sum = *sum + x;
        }
        p = p + 1;
    }

    Label_a:
    *sum += 0; // No effect, but ensures 'sum' is not modified beyond this point.
    //@ assert \at(*sum, Label_a) == count * x; // Assertion confirming the relationship between 'sum' and 'count'.
    return count;
}
