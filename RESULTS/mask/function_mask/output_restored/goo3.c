
/*@
axiomatic Array {
    logic integer store_int_array(int* arr, integer n);
    axiom store_int_array_initial:
        \forall int* arr, integer n;
            store_int_array(arr, n) ==>
            \forall integer i; 0 <= i < n ==> arr[i] == arr[i]; // No change
}
*/

/*@
requires \valid(arr + (0 .. n-1));                  // Array pointer validation
requires n > 0 && n < 100;                          // Array size constraints
requires store_int_array(arr, n);                  // Logical array initialization
ensures \forall integer i; 0 <= i < n ==> arr[i] == \old(arr[i]) + c; // Post-condition: array elements incremented by c
*/
void increment_array_by(int* arr, int n, int c) {
    /*@
    loop invariant 0 <= i <= n;                     // Loop bounds
    loop invariant \forall integer j; 0 <= j < i ==> arr[j] == \old(arr[j]) + c; // Incremental correctness during execution
    loop assigns arr[0 .. n-1];                     // Memory assignments
    loop assigns i;                                 // Loop variable assignment
    loop variant n - i;                             // Decreasing variant for termination
    */
    for (int i = 0; i < n; i++) {
        arr[i] = arr[i] + c;
    }
}

void goo3() {
    int arr[5] = {1, 2, 3, 4, 5};
    increment_array_by(arr, 5, 2);
    //@ assert arr[0] == 3;
    //@ assert arr[1] == 4;
    //@ assert arr[2] == 5;
    //@ assert arr[3] == 6;
    //@ assert arr[4] == 7;
}
