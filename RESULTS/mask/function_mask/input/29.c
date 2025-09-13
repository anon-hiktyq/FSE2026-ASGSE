void arrayDouble(int *a, unsigned int n) {
    int p = 0;

    while (p < n) {
        a[p] = a[p] * 2;
        p = p + 1;
    } 
}

int goo29() {
    int arr[] = {0,1,2,3,4,5};
    arrayDouble(arr, 6);
/* MASK_ACSL_ASSERT_LINE */
/* MASK_ACSL_ASSERT_LINE */
/* MASK_ACSL_ASSERT_LINE */
/* MASK_ACSL_ASSERT_LINE */
/* MASK_ACSL_ASSERT_LINE */
/* MASK_ACSL_ASSERT_LINE */
}