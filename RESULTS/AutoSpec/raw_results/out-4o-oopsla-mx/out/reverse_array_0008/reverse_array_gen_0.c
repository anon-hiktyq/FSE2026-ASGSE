void reverse(int *a, int n) {
    int i = 0;
    int j = n-1;

    /*@
    loop invariant 0 <= i <= n/2;
    loop invariant n/2 <= j < n;
    loop invariant i + j == n - 1;
    loop invariant \forall integer k; 0 <= k < i ==> a[k] == \old(a[n-1-k]);
    loop invariant \forall integer k; n-j-1 < k < n ==> a[k] == \old(a[n-1-k]);
    loop assigns i, j, a[0..n-1];
    */
    while (i < n/2) {
        int temp = a[i];
        a[i] = a[j];
        a[j] = temp;
        i++;
        j--;
    }
}

// write a test
void main() {
    int arr[5] = {1, 2, 3, 4, 5};
    reverse(arr, 5);
    // @ assert arr[4] == 1;
}