
int binarysearch(int* a, int x, int n) {

    int low = -1;
    int high = n;
    int p;

   
    /*@
    loop invariant p < high;
    loop invariant low < p;
    loop invariant low < high;
    loop invariant low + 1 < high;
    loop invariant low + 1 < high ==> p == (low + high) / 2;
    loop invariant high <= n;
    loop invariant \forall integer k; p < k < n ==> a[k] > x ==> high > p;
    loop invariant \forall integer k; low < k < high ==> a[k] < x;
    loop invariant \forall integer k; low < k < high ==> a[k] != x;
    loop invariant \forall integer k; low + 1 < high ==> (a[low] < x && a[high] > x);
    loop invariant \forall integer k; high <= n ==> a[k] > x;
    loop invariant \forall integer k; high <= k < n ==> a[k] > x;
    loop invariant \forall integer k; 0 <= k <= low ==> a[k] < x;
    loop invariant \forall integer k; 0 <= k < p ==> a[k] < x ==> low < p;
    loop invariant \forall integer k; 0 <= k < low + 1 ==> a[k] < x;
    loop invariant \forall integer k; 0 <= k < high ==> a[k] >= x;
    loop invariant -1 <= low;
    loop invariant (low == -1) || (high == n) || (a[low] < x);
    loop assigns p;
    loop assigns low;
    loop assigns high;
    */
    while (low+1 < high) {
        p = (low + high) / 2;
        if (a[p] == x) 
            return p;
        else 
            if (a[p] < x)
            low = p;
            else high = p;
    }
    return -1;
}

// write a test
void main() {
    int arr[5] = {1, 2, 3, 4, 5};
    int sum = binarysearch(arr, 3, 5);
  
}