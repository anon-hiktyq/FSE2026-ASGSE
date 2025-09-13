
int arraymax(int* a, int n) {
  int i = 1;
  int max = a[0];


  /*@
  loop invariant 1 <= i <= n;
  loop invariant max == \max(a[0..i-1]);
  loop assigns i;
  loop assigns max;
  */
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
void main() {
  int arr[5] = {1, 2, 3, 4, 5};
  int sum = arraymax(arr, 5);

}