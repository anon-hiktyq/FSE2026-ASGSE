int sumArray(int *a, int n) {
    int p = 0, sum = 0;

    /*@
    loop invariant sum == \sum(0, p-1, a);
    loop invariant sum == \sum(0, p, a);
    loop invariant p <= n;
    loop invariant \forall integer k; 0 <= k < p ==> sum == \sum(0, k, a);
    loop invariant \forall integer i; 0 <= i < p ==> sum == \sum(0, i, a);
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