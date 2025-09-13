
/*@
  requires \valid(a + (0 .. n-1)); // a is a valid pointer for an array of size n
  requires \valid(b + (0 .. n-1)); // b is a valid pointer for an array of size n
  requires n >= 0; // n must be non-negative

  assigns \nothing; // No global variables are modified

  ensures \result == 1 <==> (n == 0 || \forall integer i; 0 <= i < n ==> a[i] == b[i]); // Result is 1 if all elements match or both are empty
  ensures \result == 0 <==> (n > 0 && \exists integer i; 0 <= i < n && a[i] != b[i]); // Result is 0 if any mismatch exists and n is positive
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

int goo16() {
    int a[] = {1,2,3,4,5};
    int b[] = {1,2,3,4,5};
    int res = check(a, b, 5);
    //@ assert res == 1;
}
