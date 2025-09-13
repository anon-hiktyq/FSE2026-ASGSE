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
    //@ assert a == 1;
    //@ assert num == 0;
    return 0;
}