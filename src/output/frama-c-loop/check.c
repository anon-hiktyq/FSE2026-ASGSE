
/*@
  requires \valid(a + (0 .. n-1)); // a is a valid pointer for an array of size n
  requires \valid(b + (0 .. n-1)); // b is a valid pointer for an array of size n
  requires n >= 0; // n must be non-negative

  assigns \nothing; // No global variables are modified

  ensures \result == 1 <==> \forall integer i; 0 <= i < n ==> a[i] == b[i]; // Result is 1 if all elements match
  ensures \result == 0 <==> \exists integer i; 0 <= i < n && a[i] != b[i]; // Result is 0 if any mismatch exists
*/
int check(int *a, int *b, int n) {
    /*@
      loop invariant 0 <= i <= n; // i is always within bounds
      loop invariant \forall integer j; 0 <= j < i ==> a[j] == b[j]; // All elements up to i are equal
      loop invariant \valid(a + (0 .. n-1)); // a remains valid
      loop invariant \valid(b + (0 .. n-1)); // b remains valid
      loop assigns i; // Only i is modified in the loop
      loop variant n - i; // The loop progresses towards termination
    */
    for (int i = 0; i < n; i++) {
        if (a[i] != b[i]) {
            return 0;
        }
    }
    return 1;
}
