
int test(int x) {
    int a = x;
    int y = 0;

    /*@
        loop invariant a == \at(x, Pre) - y;
        loop invariant a >= 0;
        loop invariant y >= 0;
        loop assigns y, a;
    */
    while(a != 0) {
        y = y + 1;
        a = a - 1;
    }

    /*@ ensures \result == \at(x, Pre); */
    return y;
}

int goo7() {
    int num = test(3);
    //@ assert num == 3;
    return 0;
}
