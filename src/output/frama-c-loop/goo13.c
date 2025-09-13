
/*@
  requires arr != \null;                       // Pointer validation
  requires n > 0;                              // The array must have at least one element
  requires \valid(arr + (0 .. n-1));           // The array must be valid in the range [0, n-1]
  ensures \exists integer k; 0 <= k < n &&     // There exists an index k such that arr[k] == \result
          \forall integer j; 0 <= j < n ==>    // For all indices j in the range [0, n-1],
          arr[j] <= \result;                   // arr[j] is less than or equal to the result
  assigns \nothing;                            // The function does not modify any memory outside its scope
*/
int array_max_advanced(int* arr, int n) {
    int max = arr[0];
    
    /*@
      loop invariant 0 <= i <= n;              // Loop index i is within bounds
      loop invariant \forall integer k; 0 <= k < i ==> arr[k] <= max; // max is greater than or equal to all seen values
      loop invariant n == \at(n, Pre);         // n remains unchanged
      loop invariant arr == \at(arr, Pre);     // arr remains unchanged
      loop invariant \forall integer j; 0 <= j < i ==> arr[j] == \at(arr, Pre)[j]; // arr values are unchanged
      loop assigns max, i;                    // The loop modifies only max and i
      loop variant n - i;                     // The loop progresses toward termination
    */
    for (int i = 1; i < n; i++) {             // Start from index 1
        if (arr[i] > max) {
            max = arr[i];
        }
    }
    
    return max;
}

void goo13() {
    int arr[5] = {1, 2, 3, 4, 5};
    int max = array_max_advanced(arr, 5);
    //@ assert max >= arr[0];
    //@ assert max >= arr[1];
    //@ assert max >= arr[2];
    //@ assert max >= arr[3];
    //@ assert max >= arr[4];
}
