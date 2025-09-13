


/*@
axiomatic ArrayIncrement {
    logic integer store_int_array(int* array, integer size, int* snapshot) reads array[0 .. size-1];
    axiom unchanged_snapshot:
        \forall int* array, integer size, int* snapshot;
        store_int_array(array, size, snapshot) ==> \forall integer i; 0 <= i < size ==> snapshot[i] == array[i];
}
*/

/*@
requires \at(n,Pre) > 0 && \at(n,Pre) < 100; // n is within valid bounds
requires \valid(arr + (0 .. n-1)); // arr points to a valid memory block of size n
requires store_int_array(\at(arr,Pre), \at(n,Pre), arr); // Snapshot of the array is stored
requires c == \at(c,Pre); // c remains unchanged
requires n == \at(n,Pre); // n remains unchanged
requires arr == \at(arr,Pre); // arr pointer remains unchanged
ensures \forall integer i; 0 <= i < n ==> arr[i] == \at(arr[i],Pre) + c; // Each element is incremented by c
ensures \forall integer i; n <= i < \at(n,Pre) ==> arr[i] == \at(arr[i],Pre); // Elements outside the range remain unchanged
*/
void increment_array_by(int* arr, int n, int c) {
    
    /*@
    loop invariant 0 <= i <= n; // i is within valid bounds
    loop invariant \forall integer j; 0 <= j < i ==> arr[j] == \at(arr[j],Pre) + c; // Elements up to i are incremented
    loop invariant \forall integer j; i <= j < n ==> arr[j] == \at(arr[j],Pre); // Elements beyond i are unchanged
    loop invariant c == \at(c,Pre); // c remains unchanged
    loop invariant n == \at(n,Pre); // n remains unchanged
    loop invariant arr == \at(arr,Pre); // arr pointer remains unchanged
    loop assigns arr[0 .. n-1]; // Only the array elements are modified
    loop variant n - i; // The loop progresses towards termination
    */
    for (int i = 0; i < n; i++) {
        arr[i] = arr[i] + c;
    }
}

void goo15() {
    int arr[5] = {1, 2, 3, 4, 5};
    increment_array_by(arr, 5, 2);
    //@ assert arr[0] == 3;
    //@ assert arr[1] == 4;
    //@ assert arr[2] == 5;
    //@ assert arr[3] == 6;
    //@ assert arr[4] == 7;
   
}


