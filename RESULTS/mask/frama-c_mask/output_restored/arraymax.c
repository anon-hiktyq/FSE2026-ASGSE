
/*@ axiomatic Max_array {
      logic integer max(int* array, integer begin, integer end) reads array[begin .. (end-1)];
      axiom empty:
        \forall int* a, integer b, e; b >= e ==> max(a,b,e) == a[b];
      axiom range:
        \forall int* a, integer b, e; b < e ==> max(a,b,e) == (max(a,b,e-1) < a[e-1] ? a[e-1] : max(a,b,e-1));
    }
*/

/*@
  requires \valid(a + (0 .. n-1));                     // The array must be valid for the given range
  requires n > 0 && n < 100;                           // The size of the array must be between 1 and 99
  ensures \forall integer j; 0 <= j < n ==> a[j] == \at(a[j], Pre); // The input array remains unchanged
  ensures \result == max(a, 0, n);                     // The result is the maximum value in the array
*/
int arraymax(int* a, int n) {
  int i = 1;
  int max = a[0];

  /*@
    loop invariant 1 <= i <= n;                        // The loop index is within bounds
    loop invariant max == max(a, 0, i);                // `max` holds the maximum value of the array from index 0 to i-1
    loop invariant n == \at(n,Pre);                    // The size of the array remains unchanged
    loop invariant a == \at(a,Pre);                    // The pointer to the array remains unchanged
    loop invariant \forall integer j; 0 <= j < n ==> a[j] == \at(a[j], Pre); // The array elements remain unchanged
    loop assigns i, max;                               // The loop modifies only `i` and `max`
    loop variant n - i;                                // The loop progresses toward termination
  */
  while (i < n) {
    if (max < a[i])
      max = a[i];
    i = i + 1;
  }
  
  return max;
}
