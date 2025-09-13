int fun(int x, int y , int *r) {
    *r = x;
    int d = 0;

    /*@
    loop invariant *r >= 0;
    loop invariant *r < y;
    loop invariant \exists integer k; d == k && x == k * y + *r;
    loop invariant x - y * d == *r;
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