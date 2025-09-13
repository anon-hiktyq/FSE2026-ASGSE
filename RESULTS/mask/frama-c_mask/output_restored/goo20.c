
/*@
axiomatic Sum_array {
  logic integer sum(int* a, integer begin, integer end) reads a[begin .. (end-1)];
  axiom empty:
    \forall int* a, integer b, e; b >= e ==> sum(a,b,e) == 0;
  axiom range:
    \forall int* a, integer b, e; b < e ==> sum(a,b,e) == sum(a,b,e-1) + a[e-1];
}
*/

/*@ 
predicate store_int_array{L}(int* array_pre, integer n_pre, int* array) = 
  \forall integer i; 0 <= i < n_pre ==> array[i] == \at(array_pre[i],L);
*/

/*@
requires \at(n,Pre) > 0 && \at(n,Pre) < 100;
requires \valid(a + (0 .. n-1));
requires store_int_array{Pre}(\at(a,Pre), \at(n,Pre), a);
ensures \result == sum(a, 0, n);
*/
int sumArray(int *a, int n) {
    int p = 0, sum = 0;

    /*@
      loop invariant 0 <= p <= n;
      loop invariant sum == sum(a, 0, p);
      loop invariant n == \at(n,Pre);
      loop invariant a == \at(a,Pre);
      loop invariant \forall integer i; 0 <= i < p ==> a[i] == \at(a[i],Pre);
      loop assigns p, sum;
      loop variant n - p;
    */
    while (p < n) {
        sum = sum + a[p];
        p++;
    }
            
    return sum;
}

void goo20() {
    int arr[5] = {1, 2, 3, 4, 5};
    int sum = sumArray(arr, 5);
      //@ assert sum == 15;
}



