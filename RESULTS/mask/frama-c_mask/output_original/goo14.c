
/*@
axiomatic Reverse_array {
  logic integer reverse_index(integer n, integer i) = n - 1 - i;
}
*/

/*@
requires \valid(a + (0 .. n-1)); // The array must be valid within the bounds [0..n-1]
requires n > 0 && n < 100;      // The size of the array must be between 1 and 99
ensures \forall integer k; 0 <= k < n ==> a[reverse_index(n, k)] == \at(a[k], Pre); // Each element in the reversed array is placed at its reverse index from the original array
ensures n == \old(n); // The size of the array remains unchanged
ensures \valid(a + (0 .. n-1)); // The array remains valid
assigns a[0..n-1]; // The array elements are modified
*/
void reverse(int *a, int n) {
    int i = 0;
    int j = n-1;

    /*@ 
      loop invariant 0 <= i <= n/2; // i progresses from 0 to n/2
      loop invariant j == n - 1 - i; // j is always the reverse index of i
      loop invariant n == \at(n,Pre); // n remains unchanged throughout the loop
      loop invariant a == \at(a,Pre); // a remains unchanged as a pointer
      loop invariant \forall integer k; 0 <= k < i ==> a[reverse_index(n, k)] == \at(a[k], Pre); // Elements before i are correctly placed at their reverse index
      loop invariant \forall integer k; j < k < n ==> a[reverse_index(n, k)] == \at(a[k], Pre); // Elements after j are correctly placed at their reverse index
      loop assigns i, j, a[0..n-1]; // Variables and array elements that may be modified
      loop variant n/2 - i; // The loop progresses toward termination
    */
    while (i < n/2) {
        int temp = a[i];
        a[i] = a[j];
        a[j] = temp;
        i++;
        j--;
    }
}

void goo14() {
    int arr[5] = {1, 2, 3, 4, 5};
    reverse(arr, 5);
}
