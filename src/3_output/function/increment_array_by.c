
/*@
axiomatic Array {
    logic integer store_int_array(int* arr, integer n) reads arr[0 .. n-1];
    axiom store_int_array_initial:
        \forall int* arr, integer n;
            store_int_array(arr, n) ==> 
            \forall integer i; 0 <= i < n ==> arr[i] == arr[i];
}
*/

/*@
requires \valid(arr + (0 .. n-1));
requires n > 0 && n < 100;
requires c == c;
requires n == n;
requires arr == arr;
requires store_int_array(arr, n);
ensures \forall integer i; 0 <= i < n ==> arr[i] == arr[i] + c;
*/
void increment_array_by(int* arr, int n, int c) {
    /*@
    loop invariant (!(i < n)) ==> ((c == c)&&(n == n)&&(arr == arr));
    loop invariant c == c;
    loop invariant n == n;
    loop invariant arr == arr;
    loop invariant 0 <= i <= n;
    loop assigns arr[0 .. n-1], i;
    */
    for (int i = 0; i < n; i++) {
        arr[i] = arr[i] + c;
    }
}
