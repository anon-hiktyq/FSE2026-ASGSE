void func7(int *a, int n) {
    for (int i = 0; i < n; i++) {
        if (i%2==0) 
            a[i] = 0;
    }
}

// write a test
void goo7() {
    int arr[5] = {1, 2, 3, 4, 5};
    func7(arr, 5);
/* MASK_ACSL_ASSERT_LINE */
/* MASK_ACSL_ASSERT_LINE */
/* MASK_ACSL_ASSERT_LINE */
}