
int arraymax(int* a, int n) {
  int i = 1;
  int max = a[0];


  /*@
  loop invariant 1 <= i <= n;
  loop invariant max == \max_{0 \leq j < i} a[j];
  loop invariant \forall integer j; 0 <= j < i ==> a[j] <= max;
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