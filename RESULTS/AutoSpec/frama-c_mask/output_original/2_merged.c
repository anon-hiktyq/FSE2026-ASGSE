
int arraymax(int* a, int n) {
  int i = 1;
  int max = a[0];


  /*@
  loop invariant max == a[0] || \exists integer k; 0 <= k < i && max == a[k];
  loop invariant max == a[0] || (i > 0 && max >= a[0]);
  loop invariant max == a[0] || (i == 1 ==> max == a[0]);
  loop invariant \forall integer k; 0 <= k < i ==> max >= a[k];
  loop invariant \forall integer k; 0 <= k < i ==> a[k] <= max;
  loop invariant \forall integer j; 0 <= j < i ==> a[j] <= max;
  loop invariant 1 <= i;
  loop assigns max;
  loop assigns i;
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