
int fun2(int n) {
    int i = 7;
    int x = 1;

    while(i <= n) {
        x += 1;
        i += 3;
    }
    return x;
}

int goo2() {
    int a = fun2(10);
/* MASK_ACSL_ASSERT_LINE */
}