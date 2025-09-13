int sumArray(int *a, int n) {
    int p = 0, sum = 0;

    /*@
    loop invariant 0 <= p <= n;
    loop invariant sum == \sum(0, p, \lambda integer i; a[i]);
    loop assigns a[0..n-1];
    loop invariant \forall integer i; 0 <= i < p ==> sum == \sum(0, i+1, \lambda integer j; a[j]);
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