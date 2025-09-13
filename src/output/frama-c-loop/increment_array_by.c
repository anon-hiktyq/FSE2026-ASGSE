
/*@
  requires \valid(arr + (0 .. n-1));  // arr must point to a valid memory region of at least n elements
  requires n >= 0;                   // n must be non-negative
  assigns arr[0..n-1];               // Only the elements of arr[0..n-1] are modified
  ensures \forall integer k; 0 <= k < n ==> arr[k] == \old(arr[k]) + c; // Each element is incremented by c
*/
void increment_array_by(int* arr, int n, int c) {
    
    /*@
      loop invariant 0 <= i <= n;                       // Loop index i is within bounds
      loop invariant \forall integer k; 0 <= k < i ==> arr[k] == \at(arr[k], Pre) + c; // Elements up to i are updated correctly
      loop invariant \forall integer k; i <= k < n ==> arr[k] == \at(arr[k], Pre);    // Elements beyond i are unchanged
      loop assigns arr[0..n-1];                       // Only the elements of arr[0..n-1] are modified
      loop variant n - i;                             // The loop progresses toward termination
    */
    for (int i = 0; i < n; i++) {
        arr[i] = arr[i] + c;
    }
}
