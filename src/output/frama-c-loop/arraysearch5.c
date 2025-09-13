
/*@
  requires \valid(a + (0 .. n-1)); // The array 'a' must be valid for the given range
  requires n >= 0;                // The size of the array must be non-negative
  assigns \nothing;               // The function does not modify any memory
  ensures \result == 1 <==> (\exists integer i; 0 <= i < n && a[i] == x); // Returns 1 if x is found in the array
  ensures \result == 0 <==> (\forall integer i; 0 <= i < n ==> a[i] != x); // Returns 0 if x is not found
*/
int arraysearch5(int* a, int x, int n) { 
    /*@
      loop invariant 0 <= p <= n; // The loop variable 'p' is within bounds
      loop invariant \forall integer i; 0 <= i < p ==> a[i] != x; // 'x' has not been found in the checked portion of the array
      loop invariant n == \at(n,Pre); // The size of the array remains unchanged
      loop invariant x == \at(x,Pre); // The value being searched for remains unchanged
      loop invariant a == \at(a,Pre); // The array pointer remains unchanged
      loop assigns p; // The loop only modifies the variable 'p'
      loop variant n - p; // The loop progresses towards termination
    */
    for (int p = 0; p < n; p++) {
        if (x == a[p]) 
            return 1;
    }
    return 0;
}
