
/*@
axiomatic ArraySearch {
    logic boolean exists(int* array, integer n, integer x) reads array[0 .. n-1];
    axiom exists_def:
        \forall int* array, integer n, integer x;
            exists(array, n, x) <==> (\exists integer i; 0 <= i < n && array[i] == x);
}
*/

/*@ requires \valid(a + (0 .. n-1));
    requires n > 0;
    requires x > 0 && x < 100;
    ensures \result == 1 <==> exists(a, n, x);
    ensures \result == 0 <==> !exists(a, n, x);
*/
int arraysearch5(int* a, int x, int n) { 
    /*@
      loop invariant (!(p < n)) ==> ((n > 0) && (x > 0 && x < 100) && \valid(a + (0 .. n-1)));
      loop invariant n > 0;
      loop invariant x > 0 && x < 100;
      loop invariant \valid(a + (0 .. n-1));
      loop assigns p;
      loop variant n - p;
    */
    for (int p = 0; p < n; p++) {
        if (x == a[p]) 
            return 1;
    }
    return 0;
}
