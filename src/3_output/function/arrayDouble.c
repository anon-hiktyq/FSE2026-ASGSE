
/*@
axiomatic StoreArray {
    logic integer store_int_array(int* array, integer size, int* array_copy) reads array[0 .. size-1];
    
    axiom store_preserve:
        \forall int* a, integer n, int* copy;
        store_int_array(a, n, copy) ==> \forall integer i; 0 <= i < n ==> copy[i] == a[i];
}
*/

/*@
requires \valid(a + (0 .. n-1));
requires \at(n,Pre) > 0 && \at(n,Pre) < 100;
requires n == \at(n,Pre) && a == \at(a,Pre) && store_int_array(\at(a,Pre), \at(n,Pre), a);
*/
void arrayDouble(int *a, unsigned int n) {
    int p = 0;

    /*@
    loop invariant (0 < \at(n,Pre)) ==> (0 <= p <= n);
    loop invariant (!(0 < \at(n,Pre))) ==> ((p == 0) && (n == \at(n,Pre)) && (a == \at(a,Pre)));
    loop invariant n == \at(n,Pre);
    loop invariant a == \at(a,Pre);
    loop assigns a[0 .. n-1], p;
    loop variant n - p;
    */
    while (p < n) {
        a[p] = a[p] * 2;
        p = p + 1;
    }
}
