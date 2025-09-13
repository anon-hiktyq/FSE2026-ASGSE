


/*@ 
  requires \valid(a + (0 .. n-1)); // Pointer validation: a must be a valid array of size n
  requires n > 0; // The array must have at least one element
  assigns \nothing; // The function does not modify the array a or x
  ensures \result == -1 || (0 <= \result < n && a[\result] == x); // Postcondition: either x is not found, or \result is a valid index where a[\result] == x
*/
int binarysearch(int* a, int x, int n) {

    int low = -1;
    int high = n;
    int p;

    /*@
      loop invariant -1 <= low < high <= n; // Invariant: valid range for low and high
      loop invariant \forall integer i; 0 <= i <= low ==> a[i] < x; // All elements up to low are less than x
      loop invariant \forall integer i; high <= i < n ==> a[i] > x; // All elements from high are greater than x
      loop invariant n == \at(n,Pre); // n remains unchanged
      loop invariant x == \at(x,Pre); // x remains unchanged
      loop invariant \valid(a + (0 .. n-1)); // Pointer validation: a is a valid array throughout
      loop assigns low, high, p; // Variables modified within the loop
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