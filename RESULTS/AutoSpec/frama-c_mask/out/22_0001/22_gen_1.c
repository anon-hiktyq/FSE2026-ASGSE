
void func(int *a, int n) {
   
    /*@
    loop invariant 0 <= i <= n;
    loop invariant \forall integer j; 0 <= j < i ==> (j % 2 != 0 ==> a[j] == original_a[j]);
    loop invariant \forall integer j; 0 <= j < i ==> (j % 2 == 0 ==> a[j] == 0);
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