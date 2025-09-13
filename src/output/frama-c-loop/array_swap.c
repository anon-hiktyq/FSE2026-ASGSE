
/*@
  requires \valid(arr + (0 .. n-1));                  // The array must be valid for the given size
  requires 0 <= n1 < n;                              // n1 must be a valid index within bounds
  requires 0 <= n2 < n;                              // n2 must be a valid index within bounds
  assigns arr[n1], arr[n2];                          // Only arr[n1] and arr[n2] are modified
  ensures arr[n1] == \old(arr[n2]);                  // After execution, arr[n1] contains the old value of arr[n2]
  ensures arr[n2] == \old(arr[n1]);                  // After execution, arr[n2] contains the old value of arr[n1]
*/
void array_swap(int* arr, int n, int n1, int n2) {
    int temp = arr[n1];
    arr[n1] = arr[n2];
    arr[n2] = temp;
}
