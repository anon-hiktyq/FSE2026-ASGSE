
/*@
  requires \valid(a + (0 .. n-1)); // Pointer validation: 'a' must be a valid array of size 'n'
  requires n >= 0;                // Precondition: 'n' must be non-negative
  ensures \result == \sum_{i=0}^{n-1} a[i]; // Postcondition: The returned value equals the sum of all elements in 'a'
*/
int sumArray(int *a, int n) {
    int p = 0, sum = 0;

    /*@
      loop invariant 0 <= p && p <= n;                     // Loop invariant: 'p' is within bounds
      loop invariant sum == \sum_{i=0}^{p-1} a[i];         // Loop invariant: 'sum' accumulates the sum of elements from 'a[0]' to 'a[p-1]'
      loop variant n - p;                                  // Loop variant: Ensures termination
    */
    while (p < n) {
        sum = sum + a[p];
        p++;
    }

    return sum;
}

void goo20() {
    int arr[5] = {1, 2, 3, 4, 5};
    int sum = sumArray(arr, 5);
    //@ assert sum == 15;
}
