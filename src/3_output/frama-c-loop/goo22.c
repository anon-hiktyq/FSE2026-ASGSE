


/*@
  requires a != \null; // Pointer validation: the array must not be null
  requires n > 0;      // The array must have at least one element
  requires \valid(a + (0 .. n-1)); // The array must be valid for the given range

  ensures \forall integer j; 0 <= j < n ==> a[j] <= \result; // Postcondition: \result is greater than or equal to all elements in the array
  ensures \exists integer j; 0 <= j < n && a[j] == \result; // Postcondition: \result is equal to at least one element in the array
*/
int arraymax22(int* a, int n) {
  int i = 1;
  int max = a[0];

  /*@
    loop invariant 1 <= i <= n; // Loop index is within bounds
    loop invariant \forall integer j; 0 <= j <= i ==> a[j] <= max; // All elements processed so far are less than or equal to max
    loop invariant \exists integer j; 0 <= j < i && a[j] == max; // max is equal to at least one element in the processed range
    loop invariant n > 0; // Array size remains positive
    loop invariant a == \at(a, Pre); // Array pointer remains unchanged
    loop invariant n == \at(n, Pre); // Array size remains unchanged
    loop assigns i, max; // Variables modified within the loop
    loop variant n - i; // Loop progresses toward termination
  */
  while (i < n) {
    if (max < a[i]) {
      max = a[i];
    }
    i = i + 1;
  }

  return max;
}

void goo22() {
  int arr[5] = {1, 2, 3, 4, 5};
  int sum = arraymax22(arr, 5);
  //@ assert sum >= arr[0];
  //@ assert sum >= arr[1];
  //@ assert sum >= arr[2];
  //@ assert sum >= arr[3];
  //@ assert sum >= arr[4];
}