int sumArray(int *a, int n) {
    int p = 0, sum = 0;

    /*@
    loop invariant 0 <= p <= n;  
    loop invariant sum == \sum(0, p-1, a[k]);  
    loop invariant \forall integer k; 0 <= k < p ==> \exists integer x; a[k] == x;  
    loop invariant sum >= 0;
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