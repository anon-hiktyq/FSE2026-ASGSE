
/*@
axiomatic Sum_array {
    logic integer sum(int* array, integer begin, integer end) reads array[begin .. (end-1)];
    axiom empty:
        \forall int* a, integer b, e; b >= e ==> sum(a,b,e) == 0;
    axiom range:
        \forall int* a, integer b, e; b < e ==> sum(a,b,e) == sum(a,b,e-1) + a[e-1];
}
*/

/*@
requires \valid(a + (0 .. n-1));                // The array `a` must be valid for the given range
requires \valid(sum);                          // The pointer `sum` must be valid
requires n > 0 && n < 100;                     // The size of the array must be within bounds
ensures \forall integer i; 0 <= i < n ==> (a[i] == x) ==> (*sum == x * (\numof(j, 0 <= j < n && a[j] == x))); // Ensures the sum is updated correctly
ensures *sum == x * (\numof(i, 0 <= i < n && a[i] == x)); // Ensures that `*sum` equals the sum of all `x` in the array
*/
int func3(int *a, int n, int x, int *sum) {
    int p = 0;
    int count = 0;
    *sum = 0;

    /* >>> LOOP INVARIANT TO FILL <<< */
    
    /*@
      loop invariant (0 < \at(n,Pre)) ==> (0 <= p <= n);
      loop invariant (!(0 < \at(n,Pre))) ==> ((count == 0)&&(p == 0)&&(sum == \at(sum,Pre))&&(x == \at(x,Pre))&&(n == \at(n,Pre))&&(a == \at(a,Pre))&&(\at(*sum,Pre) == 0));
      loop invariant x == \at(x,Pre);
      loop invariant n == \at(n,Pre);
      loop invariant a == \at(a,Pre);
    */
    while (p < n) {
        if (a[p] == x) {
            count = count + 1;
            *sum = *sum + x;
        }
        p = p + 1;
    }
            
    Label_a:
    *sum += 0;
    
    return count;
}
