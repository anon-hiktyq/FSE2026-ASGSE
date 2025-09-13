int arraymax22(int* a, int n) {
  int i = 1;
  int max = a[0];

  while (i < n) {
    // Beginning of loop
    if (max < a[i])
    max = a[i];
    i = i + 1;
    // End of loop: Loop invariant comes here
  }
  return max;
}  

// write a test
void goo22() {
  int arr[5] = {1, 2, 3, 4, 5};
  int sum = arraymax22(arr, 5);
}