


/*@
  requires a != \null; // Pointer validation: array pointer must not be null
  requires n >= 0; // Array size must be non-negative
  requires \valid(a + (0 .. n-1)); // Array must be valid for the given size
  ensures \result == 1 <==> (n == 0 || \forall integer i; 0 <= i < n ==> a[i] % 2 == 0); // Result is 1 if all elements are even or if the array is empty
  ensures \result == 0 <==> (n > 0 && \exists integer i; 0 <= i < n && a[i] % 2 != 0); // Result is 0 if any element is odd and the array is not empty
*/
int areElementsEven(int *a, int n) {
    int p = 0;

    /*@
      loop invariant 0 <= p <= n; // Loop index is within bounds
      loop invariant \forall integer i; 0 <= i < p ==> a[i] % 2 == 0; // All checked elements are even
      loop assigns p; // Only the loop index is modified
      loop variant n - p; // Loop progresses towards termination
    */
    while (p < n) {
        if (a[p] % 2 != 0) {
            return 0;
        }
        p = p + 1;
    }

    return 1;
}

void goo25() {
    int arr[] = {2,4,6,8,10};
    int res = areElementsEven(arr, 5);
    //@ assert res == 1;
}