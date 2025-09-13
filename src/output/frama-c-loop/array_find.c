
/*@
  requires arr != \null;  // Pointer validation: arr must not be null
  requires n >= 0;       // The size of the array must be non-negative
  requires \valid(arr + (0 .. n-1));  // The array must be valid within the bounds [0, n-1]
  requires \forall integer k; 0 <= k < n ==> arr[k] == \at(arr[k], Pre); // Array elements remain unchanged during execution
  
  ensures \result == -1 ==> \forall integer k; 0 <= k < n ==> arr[k] != x; // If -1 is returned, x is not in the array
  ensures \result >= 0 ==> (0 <= \result < n && arr[\result] == x); // If a valid index is returned, arr[result] equals x
*/
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
