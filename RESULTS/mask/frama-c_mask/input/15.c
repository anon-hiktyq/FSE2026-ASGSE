void increment_array_by(int* arr, int n, int c) {
    for (int  i = 0; i < n; i++) {
        arr[i] = arr[i] + c;
    }
}

// write a test to call increment_array_by with a small array and a small constant
// and check that the array is incremented by the constant
void goo15() {
    int arr[5] = {1, 2, 3, 4, 5};
    increment_array_by(arr, 5, 2);
   
}