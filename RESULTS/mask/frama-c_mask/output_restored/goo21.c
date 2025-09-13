
/*@
axiomatic BinarySearch {
    logic integer range(int* array, integer low, integer high) reads array[low .. high-1];
    axiom range_empty:
        \forall int* a, integer l, h; l >= h ==> range(a, l, h) == 0;
    axiom range_valid:
        \forall int* a, integer l, h; l < h ==> range(a, l, h) == range(a, l, h-1) + a[h-1];
}
*/

/*@
requires \valid(a + (0 .. n-1)); // The array must be valid for reading in the range [0, n-1]
requires n > 0; // The array size must be positive
requires \forall integer i; 0 <= i < n-1 ==> a[i] <= a[i+1]; // The array must be sorted in non-decreasing order
requires \at(x,Pre) > 0 && \at(x,Pre) < 100; // The target value x must be within the range (0, 100)
ensures \result == -1 || (0 <= \result < n && a[\result] == x); // If x is found, return an index where a[result] == x, else return -1
ensures \result == -1 ==> (\forall integer i; 0 <= i < n && a[i] != x); // If x is not in the array, return -1
ensures n == \at(n,Pre); // The size of the array remains unchanged
ensures \valid(a + (0 .. n-1)); // The validity of the array remains unchanged
*/
int binarysearch(int* a, int x, int n) {

    int low = -1;
    int high = n;
    int p;

    /*@ 
        loop invariant -1 <= low < high <= n; // The search range is valid
        loop invariant \valid(a + (0 .. n-1)); // The array remains valid for reading
        loop invariant n == \at(n,Pre); // The size of the array remains unchanged
        loop invariant x == \at(x,Pre); // The target value x remains unchanged
        loop invariant a == \at(a,Pre); // The array pointer remains unchanged
        loop invariant low == -1 || (\forall integer i; 0 <= i <= low ==> a[i] < x); // All elements in the range [0, low] are less than x
        loop invariant high == n || (\forall integer i; high <= i < n ==> a[i] > x); // All elements in the range [high, n-1] are greater than x
        loop variant high - low; // The distance between high and low decreases with each iteration
    */
    while (low+1 < high) {
        p = (low + high) / 2;
        if (a[p] == x) 
            return p;
        else 
            if (a[p] < x)
                low = p;
            else 
                high = p;
    }
            
    return -1;
}

void goo21() {
    int arr[5] = {1, 2, 3, 4, 5};
    int sum = binarysearch(arr, 3, 5);
      //@ assert arr[sum] == 3;
}



