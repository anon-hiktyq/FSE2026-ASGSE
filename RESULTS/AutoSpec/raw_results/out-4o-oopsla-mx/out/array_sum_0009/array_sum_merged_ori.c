int sumArray(int *a, int n) {
    int p = 0, sum = 0;

    /*@
    loop invariant sum == \sum(0, p-1, a[k]);;
    loop invariant sum == \sum(0, p-1, a[k]);
    loop invariant sum == \sum(0, p-1, a);
    loop invariant sum == \sum(0, p, a);
    loop invariant p == n ==> sum == \sum(0, n-1, a);
    loop invariant p <= n;;
    loop invariant p <= n;
    loop invariant \forall integer k; 0 <= k < p ==> sum >= a[k];
    loop invariant \forall integer k; 0 <= k < p ==> sum == \sum(0, k, a[j]);
    loop invariant \forall integer k; 0 <= k < p ==> sum == \sum(0, k+1, a);
    loop invariant \forall integer k; 0 <= k < p ==> a[k] >= 1;
    loop invariant \forall integer k; 0 <= k < p ==> a[k] >= 0;;
    loop invariant \forall integer k; 0 <= k < p ==> a[k] >= 0;
    loop invariant \forall integer k; 0 <= k < p ==> a[k] == arr[k];
    loop invariant \forall integer k; 0 <= k < p ==> \exists integer x; a[k] == x;;
    loop invariant \exists integer k; 0 <= k < p ==> sum == \sum(0, k, a);
    loop invariant \exists integer k; 0 <= k < n ==> sum >= a[k];
    loop invariant 0; <= sum;
    loop invariant 0 <= sum;
    loop invariant \forall integer k; 0 <= k < p ==> \exists integer x; a[k] == x;
    loop invariant 0 <= p;
    loop assigns sum;
    loop assigns p;
    */
    while (p < n) {
        sum = sum + a[p];
        p++;
    }
    return sum;
}

// write a test
void main() {
    int arr[5] = {1, 2, 3, 4, 5};
    int sum = sumArray(arr, 5);
    // @ assert sum == 15;
}