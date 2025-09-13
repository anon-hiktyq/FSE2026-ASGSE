
/*@
axiomatic ArrayIncrement {
    logic integer store_int_array(int* array, integer size, int* snapshot) reads array[0 .. size-1];
    axiom unchanged_snapshot:
        \forall int* array, integer size, int* snapshot;
        store_int_array(array, size, snapshot) ==> \forall integer i; 0 <= i < size ==> snapshot[i] == array[i];
}
*/

/*@
requires \at(n,Pre) > 0 && \at(n,Pre) < 100 && (c == \at(c,Pre)) && (n == \at(n,Pre)) && (arr == \at(arr,Pre)) && store_int_array(\at(arr,Pre), \at(n,Pre), arr);
*/
void increment_array_by(int* arr, int n, int c) {
    
    /*@
    loop invariant (!(i < \at(n,Pre))) ==> ((c == \at(c,Pre)) && (n == \at(n,Pre)) && (arr == \at(arr,Pre)));
    loop invariant c == \at(c,Pre);
    loop invariant n == \at(n,Pre);
    loop invariant arr == \at(arr,Pre);
    */
    for (int i = 0; i < n; i++) {
        arr[i] = arr[i] + c;
    }
}
