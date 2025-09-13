
int array_max_advanced(int* arr, int n) {
    int max = arr[0];
    
            
        /* >>> LOOP INVARIANT TO FILL <<< */
        
            /*@
          loop invariant n == \at(n,Pre);
          loop invariant arr == \at(arr,Pre);
          loop invariant \forall integer j; 0 <= j < i ==> arr[j] == \at(arr,Pre)[j];
          loop assigns max, i;
            */
            for (int i = 0; i < n; i++) {
        if (arr[i] > max) {
            max = arr[i];
        }
    }
            
    return max;
}
