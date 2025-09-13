


/*@
  requires arr != \null;                            // The pointer 'arr' must be valid.
  requires n > 0;                                   // The array size 'n' must be positive.
  requires 0 <= n1 < n;                             // Index 'n1' must be within bounds.
  requires 0 <= n2 < n;                             // Index 'n2' must be within bounds.
  assigns arr[n1], arr[n2];                         // The function modifies 'arr[n1]' and 'arr[n2]'.
  ensures arr[n1] == \old(arr[n2]);                 // After the swap, 'arr[n1]' contains the old value of 'arr[n2]'.
  ensures arr[n2] == \old(arr[n1]);                 // After the swap, 'arr[n2]' contains the old value of 'arr[n1]'.
*/
void array_swap(int* arr, int n, int n1, int n2) {
    int temp = arr[n1];
    arr[n1] = arr[n2];
    arr[n2] = temp;
}

void goo27() {
    int arr[5] = {1, 2, 3, 4, 5};
    array_swap(arr, 5, 0, 4);
}