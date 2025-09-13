// Program to swap 2 elements of an array at the givem indices n1, n2

void array_swap(int* arr, int n, int n1, int n2) {
    int temp = arr[n1];
    arr[n1] = arr[n2];
    arr[n2] = temp;
}

// write a test
void goo16() {
    int arr[5] = {1, 2, 3, 4, 5};
    array_swap(arr, 5, 0, 4);
/* MASK_ACSL_ASSERT_LINE */
/* MASK_ACSL_ASSERT_LINE */
/* MASK_ACSL_ASSERT_LINE */
/* MASK_ACSL_ASSERT_LINE */
/* MASK_ACSL_ASSERT_LINE */
}