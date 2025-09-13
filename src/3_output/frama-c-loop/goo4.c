


/*@ 
  requires \valid(a + (0 .. n-1)); // Ensure the array 'a' is valid for the range 0 to n-1
  requires n >= 0; // Ensure 'n' is non-negative
  assigns \nothing; // Function does not modify any global state
  ensures \result == 1 <==> \exists integer i; 0 <= i < n && a[i] == x; // Postcondition: x is found within the array
  ensures \result == 0 <==> \forall integer i; 0 <= i < n ==> a[i] != x; // Postcondition: x is not found within the array
*/
int arraySearch4(int *a, int x, int n) {
    int p = 0;

    /*@
      loop invariant 0 <= p <= n; // p is within the bounds of the array
      loop invariant \forall integer i; 0 <= i < p ==> a[i] != x; // x has not been found in the range 0 to p-1
      loop assigns p; // p is the only variable modified in the loop
      loop variant n - p; // Loop variant to ensure termination
    */
    while (p < n) {
        if (a[p] == x) {
            return 1;
        }
        p++;
    }
    
    return 0;
}

void goo4() {
    int arr[5] = {1, 2, 3, 4, 5};
    int sum = arraySearch4(arr, 3, 5);
    //@ assert sum == 1;
}