
int array_find(int* arr, int n, int x) {
    int i = 0;

    /*@
      loop invariant (0 < \at(n,Pre)) ==> (i >= 0 && i <= \at(n,Pre));
      loop invariant (!(0 < \at(n,Pre))) ==> (i == 0 && x == \at(x,Pre) && n == \at(n,Pre) && arr == \at(arr,Pre));
      loop invariant x == \at(x,Pre);
      loop invariant n == \at(n,Pre);
      loop invariant \forall integer k; 0 <= k < i ==> arr[k] == \at(arr[k], Pre);
      loop assigns i;
    */
    for (i = 0; i < n; i++) {
        if (arr[i] == x) {
            return i;
        }
    }

    return -1;
}
