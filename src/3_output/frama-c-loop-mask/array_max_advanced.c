
/*@ axiomatic Max_array {
      logic integer max(int* array, integer begin, integer end) reads array[begin .. (end-1)];
      axiom empty:
        \forall int* a, integer b, e; b >= e ==> max(a,b,e) == a[b];
      axiom range:
        \forall int* a, integer b, e; b < e ==> max(a,b,e) == (max(a,b,e-1) > a[e-1] ? max(a,b,e-1) : a[e-1]);
    }
*/

/*@
requires \valid(arr + (0 .. n-1));
requires \at(n,Pre) > 0 && \at(n,Pre) < 100;
*/
int array_max_advanced(int* arr, int n) {
    int max = arr[0];
    
    /*@
      loop invariant n == \at(n,Pre);
      loop invariant arr == \at(arr,Pre);
      loop invariant \forall integer k; 0 <= k < n ==> arr[k] == \at(arr[k], Pre);
    */
    for (int i = 0; i < n; i++) {
        if (arr[i] > max) {
            max = arr[i];
        }
    }
            
    return max;
}
