


/*@
  requires \valid(arr + (0 .. n-1));  // arr must point to a valid array of size n
  requires 0 <= n1 < n;              // n1 must be a valid index within the array bounds
  requires 0 <= n2 < n;              // n2 must be a valid index within the array bounds
  assigns arr[n1], arr[n2];          // Only arr[n1] and arr[n2] are modified
  ensures arr[n1] == \old(arr[n2]);  // After the swap, arr[n1] contains the old value of arr[n2]
  ensures arr[n2] == \old(arr[n1]);  // After the swap, arr[n2] contains the old value of arr[n1]
*/
void array_swap(int* arr, int n, int n1, int n2) {
    int temp = arr[n1];
    arr[n1] = arr[n2];
    arr[n2] = temp;
}

void goo16() {
    int arr[5] = {1, 2, 3, 4, 5};
    array_swap(arr, 5, 0, 4);
/* MASK_ACSL_ASSERT_LINE */
/* MASK_ACSL_ASSERT_LINE */
/* MASK_ACSL_ASSERT_LINE */
/* MASK_ACSL_ASSERT_LINE */
/* MASK_ACSL_ASSERT_LINE */
}