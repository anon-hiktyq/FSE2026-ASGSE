

int fun6(int x) {
    int a = x;
    int y = 0;

    while(a != 0) {
        y = y + 1;
        a = a - 1;
    }
    return y;
}
    
int goo6() {
    int num = fun6(3);
/* MASK_ACSL_ASSERT_LINE */
    return 0;
}