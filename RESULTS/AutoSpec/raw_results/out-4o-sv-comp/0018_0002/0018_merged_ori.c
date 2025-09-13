
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
    loop invariant i <= j;
    loop invariant i % 2 == j % 2;
    loop invariant i % 2 == 0;
    loop invariant i % 2 == 0 || i % 2 == 1;
    loop invariant flag ==> a == b;
    loop invariant b == a * (j - i);
    loop invariant b == a * (j - i) / a - 1;
    loop invariant b == a * (j - i) / (i + 1);
    loop invariant b <= a;
    loop invariant 1 <= j;
    loop invariant 0 <= i;
    loop invariant 0 <= b;
    loop invariant 0 <= a;
    loop invariant (i % 2 == 1) <==> (j % 2 == 1);
    loop invariant (i % 2 == 0) <==> (j % 2 == 0);
    loop invariant (i % 2 == 0 && j % 2 == 0) || (i % 2 == 1 && j % 2 == 1);
    loop invariant (flag ==> a - b == 0) || (!flag ==> a - b >= 0);
    loop invariant (flag ==> (j - i) % 2 == 0);
    loop invariant (flag ==> (b == a + j - i - 1));
    loop invariant ((i % 2 == 0) ==> j % 2 == 0) || ((i % 2 == 1) ==> j % 2 == 1);
    loop invariant (!flag ==> (b == a + j - i));
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
