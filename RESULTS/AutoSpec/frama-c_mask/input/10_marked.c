
/* 2. FUNC CONTRACT */
int array_max_advanced(int* arr, int n) {
    int max = arr[0];
   
    /* 1. LOOP INVARIANT */
    for (int i = 0; i < n; i++) {
        if (arr[i] > max) {
            max = arr[i];
        }
    }
    return max;
}

// write a test
/* 3. FUNC CONTRACT */
void main() {
    int arr[5] = {1, 2, 3, 4, 5};
    int max = array_max_advanced(arr, 5);

}