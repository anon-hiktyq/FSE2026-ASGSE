
void func(int *a, int n) {
   
    /*@
    loop invariant i <= n;
    loop invariant \forall integer k; 0 <= k < i ==> a[k] == (k % 2 == 0 ? 0 : arr[k]);
    loop invariant \forall integer k; 0 <= k < i ==> (k % 2 == 1 ==> a[k] == original_value);
    loop invariant \forall integer k; 0 <= k < i ==> (k % 2 == 1 ==> a[k] == 1 || a[k] == 2 || a[k] == 3 || a[k] == 4 || a[k] == 5);
    loop invariant \forall integer k; 0 <= k < i ==> (k % 2 == 0 ==> a[k] == 0);
    loop invariant \forall integer k; 0 <= k < i && k % 2 == 0 ==> a[k] == 0;
    loop invariant \forall integer j; 0 <= j < i ==> (j % 2 == 1 ==> a[j] == original_a[j]);
    loop invariant \forall integer j; 0 <= j < i ==> (j % 2 == 0 ==> a[j] == 0);
    loop invariant \forall integer j; 0 <= j < i ==> (j % 2 != 0 ==> a[j] == original_a[j]);
    loop invariant 0 <= i;
    loop assigns i;
    loop assigns a[0..n-1];
    */
    for (int i = 0; i < n; i++) {
        if (i%2==0) 
            a[i] = 0;
    }
}

// write a test
void main() {
    int arr[5] = {1, 2, 3, 4, 5};
 
}