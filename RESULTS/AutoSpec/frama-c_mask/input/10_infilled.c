
int array_max_advanced(int* arr, int n) {
    int max = arr[0];
   
    /* @ >>> INFILL <<< */
    for (int i = 0; i < n; i++) {
        if (arr[i] > max) {
            max = arr[i];
        }
    }
    return max;
}

// write a test
void main() {
    int arr[5] = {1, 2, 3, 4, 5};
    int max = array_max_advanced(arr, 5);

}