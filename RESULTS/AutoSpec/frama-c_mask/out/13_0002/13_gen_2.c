#include <stdio.h>


void bubbleSort(int *a, int n) {
    if (n <= 0) return;
    int i, j, temp;

    for(i=n-1; i>0; i--) {
       
        /*@
        loop invariant 0 <= i < n;
        loop invariant i >= 0;
        loop invariant i < n;
        loop invariant i >= 0;
        loop invariant \forall integer k; 0 <= k <= j < i ==> a[k] <= a[j];
        loop invariant \forall integer k; 0 <= k < i+1 < n ==> a[k] <= a[i+1];
        loop invariant \forall integer k; 0 <= k < i+1 < n ==> a[k] <= a[i+1];
        loop assigns temp;
        loop assigns j;
        loop assigns i;
        loop assigns a[0..n-1];
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

// write a test
void main() {
    int arr[5] = {5, 4, 3, 2, 1};
    bubbleSort(arr, 5);
   
}