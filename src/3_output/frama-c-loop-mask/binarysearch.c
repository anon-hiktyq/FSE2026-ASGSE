
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
requires \valid(a + (0 .. n-1));
requires n > 0;
requires \forall integer i; 0 <= i < n-1 ==> a[i] <= a[i+1];
requires \at(x,Pre) > 0 && \at(x,Pre) < 100;
*/
int binarysearch(int* a, int x, int n) {

    int low = -1;
    int high = n;
    int p;

    /*@ 
        loop invariant -1 <= low < high <= n;
        loop invariant \valid(a + (0 .. n-1));
        loop invariant n == \at(n,Pre);
        loop invariant x == \at(x,Pre);
        loop invariant a == \at(a,Pre);
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
