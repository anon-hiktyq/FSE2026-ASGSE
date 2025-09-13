
/*@
axiomatic StoreIntArray {
    logic boolean store_int_array(int* original, integer size, int* current) reads original[0 .. size-1], current[0 .. size-1];
    axiom store_int_array_initial:
      \forall int* a, integer n; store_int_array(a, n, a);
    axiom store_int_array_update:
      \forall int* a, integer n, integer i, integer v;
      0 <= i < n ==> store_int_array(a, n, a) && a[i] == v;
}
*/

/*@
requires \valid(a + (0 .. n-1));              // Array 'a' must be valid for the range [0 .. n-1].
requires n > 0 && n < 100;                   // 'n' must be positive and less than 100.
requires store_int_array(a, n, a);           // Logical property about the array's state.
ensures \forall integer i; 0 <= i < n ==> (i % 2 == 0 ? a[i] == 0 : a[i] == \old(a[i])); // Even indices are set to 0, odd indices remain unchanged.
assigns a[0 .. n-1];                          // Function modifies the array elements.
*/
void func7(int *a, int n) {
    /*@
    loop invariant 0 <= i <= n;              // Loop index 'i' is within bounds.
    loop invariant \forall integer j; 0 <= j < i ==> (j % 2 == 0 ? a[j] == 0 : a[j] == \at(a[j],Pre)); // Even indices set to 0, odd indices unchanged.
    loop invariant \forall integer j; i <= j < n ==> (j % 2 == 0 ? \at(a[j],Pre) == \at(a[j],Pre) : a[j] == \at(a[j],Pre)); // Odd indices remain unchanged.
    loop invariant n == \at(n,Pre);          // 'n' remains unchanged throughout the loop.
    loop invariant a == \at(a,Pre);          // Pointer 'a' remains unchanged throughout the loop.
    loop assigns a[0 .. n-1], i;             // Loop modifies the array elements and the index 'i'.
    */
    for (int i = 0; i < n; i++) {
        if (i % 2 == 0) 
            a[i] = 0;
    }
}
