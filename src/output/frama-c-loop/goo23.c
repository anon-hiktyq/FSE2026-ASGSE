
void bubbleSort(int *a, int n) 
{
    if (n <= 0) return;
    int i, j, temp;

    /*@
      requires n >= 0;
      assigns a[0..n-1];
      loop invariant 0 <= i <= n;
      loop invariant \forall int k; 0 <= k < n - 1 ==> a[k] <= a[k + 1];
    */
    for(i=n-1; i>0; i--) {
        /*@
          loop invariant 0 <= j <= i;
          loop invariant \forall int k; 0 <= k < i ==> a[k] <= a[k + 1];
        */
        for(j=0; j<i; j++) {
            if (a[j] > a[j+1]) {
                temp = a[j];
                a[j] = a[j+1];
                a[j+1] = temp;
            }
        }
    }
}

void goo23() {
    int arr[5] = {5, 4, 3, 2, 1};
    bubbleSort(arr, 5);
    //@ assert \forall int i; 0 <= i < 4 ==> arr[i] <= arr[i+1];
    //@ assert \forall int i; 0 <= i < 5 - 1 ==> arr[i] <= arr[i+1];
}
