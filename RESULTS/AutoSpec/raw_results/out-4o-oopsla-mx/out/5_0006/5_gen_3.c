int fun(int x, int y , int *r) {
    *r = x;
    int d = 0;

    /*@
    loop invariant *r >= 0;
    loop invariant *r < y;
    loop invariant d*y + *r == x;
    loop invariant d >= 0;
    loop assigns *r;
    loop assigns d;
    */
    while (*r >= y) {
        *r = *r - y;
        d = d + 1;
    }
    return d;
}

int main() {
    int a = 3;
    int num = fun(1, 2, &a);
    // @ assert a == 1;
    // @ assert num == 0;
    return 0;
}