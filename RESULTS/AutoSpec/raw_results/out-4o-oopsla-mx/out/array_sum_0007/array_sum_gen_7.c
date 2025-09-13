int sumArray(int *a, int n) {
    int p = 0, sum = 0;

    /*@
    loop invariant 0 <= p <= n;
    loop invariant sum == \sum(0, p-1, a);
    loop invariant \forall integer k; 0 <= k < p ==> sum == \sum(0, p-1, a);
    loop assigns p;
    loop assigns sum;
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