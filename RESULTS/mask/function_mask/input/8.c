void swap(int* a, int* b) {
    int tmp = *a;
    *a = *b;
    *b = tmp;
}

int goo8(){
    int a = 37;
    int b = 91;
    swap(&a, &b);
/* MASK_ACSL_ASSERT_LINE */
/* MASK_ACSL_ASSERT_LINE */
    return 0;
}