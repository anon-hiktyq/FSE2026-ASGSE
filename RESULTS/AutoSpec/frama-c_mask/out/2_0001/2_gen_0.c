
int arraymax(int* a, int n) {
  int i = 1;
  int max = a[0];


  /*@
  loop invariant 1 <= i <= n;
  loop invariant max == \max_{0 <= k < i}(a[k]);
  loop invariant \forall integer k; 0 <= k < i ==> a[k] <= max;
  loop assigns i;
  loop assigns max;
  */
  while (i < n) {
    if (max < a[i])
    max = a[i];
    i = i + 1;
  }
  return max;
}

void main() {
  int arr[5] = {1, 2, 3, 4, 5};
  int max = arraymax(arr, 5);
}