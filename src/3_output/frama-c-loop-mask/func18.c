
/*@
axiomatic Store_Int_Array {
    logic integer store_int_array(int* array, integer size, int* ref) reads array[0..size-1];
    axiom store_preserve:
        \forall int* array, integer size, int* ref; store_int_array(array, size, ref) == store_int_array(ref, size, ref);
}
*/

/*@
requires \at(n,Pre) > 0 && \at(n,Pre) < 100 && (n == \at(n,Pre)) && (a == \at(a,Pre)) && store_int_array(\at(a,Pre), \at(n,Pre), a);
*/
void func18(int *a, int n) {
    /*@
    loop invariant (!(i < \at(n,Pre))) ==> ((n == \at(n,Pre))&&(a == \at(a,Pre)));
    loop invariant n == \at(n,Pre);
    loop invariant a == \at(a,Pre);
    */
    for (int i = 0; i < n; i++) {
        if (i % 2 == 0) 
            a[i] = 0;
    }
}
