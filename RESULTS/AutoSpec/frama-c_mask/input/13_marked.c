#include <stdio.h>


/* 3. FUNC CONTRACT */
void bubbleSort(int *a, int n) {
    if (n <= 0) return;
    int i, j, temp;

    /* 2. LOOP INVARIANT */
    for(i=n-1; i>0; i--) {
       
        /* 1. LOOP INVARIANT */
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
/* 4. FUNC CONTRACT */
void main() {
    int arr[5] = {5, 4, 3, 2, 1};
    bubbleSort(arr, 5);
   
}