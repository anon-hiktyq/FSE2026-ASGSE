
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
requires \valid(a + (0 .. n-1));
requires n > 0 && n < 100;
requires store_int_array(a, n, a);
*/
void func7(int *a, int n) {
    /*@
    loop invariant (!(i < \at(n,Pre))) ==> ((n == \at(n,Pre)) && (a == \at(a,Pre)));
    loop invariant n == \at(n,Pre);
    loop invariant a == \at(a,Pre);
    loop assigns a[0 .. n-1], i;
    */
    for (int i = 0; i < n; i++) {
        if (i % 2 == 0) 
            a[i] = 0;
    }
}
