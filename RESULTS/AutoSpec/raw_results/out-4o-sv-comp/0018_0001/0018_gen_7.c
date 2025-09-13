
int unknown1();

void foo0018(int flag) {
    unsigned int i, j, a, b;
    a = 0;
    b = 0;
    j = 1;
    if (flag) {
        i = 0;
    } else {
        i = 1;
    }

    
    /*@
    loop invariant a >= b;
    loop invariant a == b + (j - i);
    loop invariant (i % 2 == 0) ==> j == i + 1;
    loop invariant (i % 2 != 0) ==> j == i;
    loop invariant a + b >= 0;
    loop assigns a;
    loop assigns b;
    loop assigns i;
    loop assigns j;
    */
    while (unknown1()) {
        a++;
        b += (j - i);
        i += 2;
        if (i % 2 == 0) {
            j += 2;
        } else {
            j++;
        }
    }
    if (flag) {
        // @ assert a == b;
    }

}
