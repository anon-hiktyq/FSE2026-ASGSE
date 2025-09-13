int fun1(int x, int y , int *r) {
    *r = x;
    int d = 0;

    while (*r >= y) {
        *r = *r - y;
        d = d + 1;
    }
    return d;
}

int goo1() {
    int a = 3;
    int num = fun1(1, 2, &a);
/* MASK_ACSL_ASSERT_LINE */
/* MASK_ACSL_ASSERT_LINE */
    return 0;
}