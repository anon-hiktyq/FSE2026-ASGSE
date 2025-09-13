
/*@ 
  requires a != \null; // The pointer 'a' must not be null
  requires n > 0; // The array must have at least one element
  requires \valid(a + (0 .. n-1)); // The array 'a' must be valid for 'n' elements
  ensures \result == \max_set(a, n); // The result is the maximum element in the array
  ensures \forall integer j; 0 <= j < n ==> \result >= a[j]; // The result is greater than or equal to all elements in the array
*/
int arraymax(int* a, int n) {
  int i = 1;
  int max = a[0];

  /*@
    loop invariant 1 <= i <= n; // Loop index 'i' is within bounds
    loop invariant \forall integer j; 0 <= j < i ==> a[j] <= max; // All processed elements are less than or equal to max
    loop invariant max == \max_set(a, i); // The current max is the maximum of the processed subarray
    loop variant n - i; // Ensure the loop will terminate
  */
  while (i < n) {
    if (max < a[i]) {
      max = a[i];
    }
    i = i + 1;
  }

  return max;
}
