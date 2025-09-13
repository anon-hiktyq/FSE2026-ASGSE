
/*@
axiomatic StoreArray {
    logic integer store_int_array(int* array, integer size, int* array_copy) reads array[0 .. size-1];
    
    axiom store_preserve:
        \forall int* a, integer n, int* copy;
        store_int_array(a, n, copy) ==> (\forall integer i; 0 <= i < n ==> copy[i] == a[i]);
}
*/

/*@
requires \valid(a + (0 .. n-1));
requires n > 0 && n < 100;
ensures \forall integer i; 0 <= i < n ==> a[i] == 2 * \at(a[i],Pre);
assigns a[0 .. n-1];
*/
void arrayDouble(int *a, unsigned int n) {
    int p = 0;

    /*@
    loop invariant 0 <= p <= n;
    loop invariant \forall integer i; 0 <= i < p ==> a[i] == 2 * \at(a[i],Pre);
    loop assigns a[0 .. n-1], p;
    loop variant n - p;
    */
    while (p < n) {
        a[p] = a[p] * 2;
        p = p + 1;
    }
}

/*@
requires \valid(arr + (0 .. 5));
ensures \forall integer i; 0 <= i < 6 ==> arr[i] == 2 * \at(arr[i],Pre);
*/
int goo29() {
    int arr[] = {0,1,2,3,4,5};
    /*@
    ensures \forall integer i; 0 <= i < 6 ==> arr[i] == 2 * \at(arr[i],Pre);
    */
    arrayDouble(arr, 6);
}
