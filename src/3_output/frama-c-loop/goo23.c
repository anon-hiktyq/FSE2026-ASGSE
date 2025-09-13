




void bubbleSort(int *a, int n) 
{
    if (n <= 0) return;
    int i, j, temp;

    
            
        /* >>> LOOP INVARIANT TO FILL <<< */
        
            /*@
            \forall int k; 0 <= k < n - 1 ==> a[k] <= a[k + 1];
            */
            for(i=n-1; i>0; i--) {
        
        /* >>> LOOP INVARIANT TO FILL <<< */
        
            /*@
            \forall int k; 0 <= k < i - 1 ==> a[k] <= a[k + 1];
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
}