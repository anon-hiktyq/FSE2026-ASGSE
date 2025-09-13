
int arraymax(int* a, int n) {
  int i = 1;
  int max = a[0];


  /*@
  loop invariant a[0] <= max;
  loop invariant \forall integer k; 1 <= k < i ==> max >= a[k];
  loop invariant \forall integer j; 0 <= j < i ==> a[j] <= max;
  loop invariant 1 <= i;
  loop assigns max;
  loop assigns i;
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