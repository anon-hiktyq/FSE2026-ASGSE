
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
    loop invariant i == 2*a + (flag ? 0 : 1);
    loop invariant i % 2 == 0 ==> j % 2 == 0;
    loop invariant i % 2 == 0 <==> j % 2 == 0;
    loop invariant i % 2 != 0 ==> j % 2 == 1;
    loop invariant flag ==> a == b;
    loop invariant flag ==> (a == b);
    loop invariant b == a * (j - i);
    loop invariant b <= a;
    loop invariant a == b + i - j;
    loop invariant a == b + (j - i);
    loop invariant a + 1 <= j;
    loop invariant 1 <= j;
    loop invariant 0 <= i;
    loop invariant 0 <= b;
    loop invariant 0 <= a;
    loop invariant 0 <= a + b;
    loop invariant (i % 2 == 1) ==> j > i;
    loop invariant (i % 2 == 0) ==> j >= i;
    loop invariant (i % 2 == 0) ==> j == i + 1;
    loop invariant (i % 2 == 0) ==> j % 2 == 0;;
    loop invariant (i % 2 == 0) ==> (j % 2 == 0);
    loop invariant (i % 2 == 0 && j % 2 == 0) || (i % 2 == 1 && j % 2 == 1);
    loop invariant (i % 2 != 0) ==> j == i;
    loop invariant (i % 2 != 0) ==> j % 2 != 0;;
    loop invariant (i % 2 != 0) ==> (j % 2 != 0);
    loop invariant !flag ==> (b + i - j >= 0);
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
