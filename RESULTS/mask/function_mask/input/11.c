int goo11(int x, int y) {
    int r = x;
    int d = 0;

    while (r >= y) {
       
        // Beginning
        r = r - y;
        d = d + 1;
        // ENd
/* MASK_ACSL_ASSERT_LINE */
    }
    return d;
}