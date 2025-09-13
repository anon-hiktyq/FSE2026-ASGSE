
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
    loop invariant a >= 0;
    loop invariant b == a * (j - i);
    loop invariant i >= 0;
    loop invariant j >= 0;
    loop invariant i % 2 == 0 ==> j >= i;
    loop invariant i % 2 == 1 ==> j >= i - 1;
    loop invariant 0 <= j;
    loop invariant 0 <= i;
    loop invariant 0 <= a;
    loop assigns j;
    loop assigns i;
    loop assigns b;
    loop assigns a;
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
