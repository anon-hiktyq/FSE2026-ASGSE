int incr_a_by_b(int* a, int * b){
    *a += *b;
    return *a;
}

// write a test
void goo10() {
    int a = 10;
    int b = 20;
    incr_a_by_b(&a, &b);
/* MASK_ACSL_ASSERT_LINE */
/* MASK_ACSL_ASSERT_LINE */
}