
int array_max_advanced(int* arr, int n) {
    int max = arr[0];
   
    /*@
    loop invariant 0 <= i <= n;
    loop invariant max >= arr[0]; 
    loop invariant \forall integer k; 0 <= k < i ==> max >= arr[k];
    loop assigns i;
    loop assigns max;
    */
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