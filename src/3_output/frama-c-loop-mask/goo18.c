


/*@
axiomatic Store_Int_Array {
    logic integer store_int_array(int* array, integer size, int* ref) reads array[0..size-1];
    axiom store_preserve:
        \forall int* array, integer size, int* ref; store_int_array(array, size, ref) == store_int_array(ref, size, ref);
}
*/

/*@
requires a != \null;                       // Pointer validation: 'a' must not be null
requires n > 0 && n < 100;                 // 'n' must be a positive integer less than 100
requires \valid(a + (0 .. n-1));           // 'a' must point to a valid memory region of size 'n'
requires store_int_array(a, n, a);         // Logical condition on the array
ensures \forall integer k; 0 <= k < n ==>  // Postcondition: for all indices in range
            (k % 2 == 0 ==> a[k] == 0) &&  // Elements at even indices are set to 0
            (k % 2 != 0 ==> a[k] == \old(a[k])); // Elements at odd indices remain unchanged
ensures n == \old(n);                      // 'n' remains unchanged
ensures a == \old(a);                      // 'a' pointer remains unchanged
*/
void func18(int *a, int n) {
    /*@
    loop invariant 0 <= i <= n;                  // Loop index 'i' is within bounds
    loop invariant \forall integer k; 0 <= k < i ==> 
                   (k % 2 == 0 ==> a[k] == 0) && // Elements at even indices up to 'i' are 0
                   (k % 2 != 0 ==> a[k] == \at(a[k], Pre)); // Odd indices are unchanged
    loop invariant n == \at(n, Pre);            // 'n' remains unchanged during the loop
    loop invariant a == \at(a, Pre);            // 'a' pointer remains unchanged during the loop
    loop assigns a[0 .. n-1];                   // The loop modifies the array elements
    loop variant n - i;                         // Loop variant decreases with each iteration
    */
    for (int i = 0; i < n; i++) {
        if (i % 2 == 0) 
            a[i] = 0;
    }
}

void goo18() {
    int arr[5] = {1, 2, 3, 4, 5};
    func18(arr, 5);
 
}