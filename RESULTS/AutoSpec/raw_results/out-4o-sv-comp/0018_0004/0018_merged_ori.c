
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
    loop invariant i >= 0 && j >= 0;
    loop invariant i <= j;
    loop invariant i % 2 == 1 || j == i + 2;
    loop invariant i % 2 == 1 ==> j >= i - 1;
    loop invariant i % 2 == 0 || j == i + 1;
    loop invariant i % 2 == 0 || i % 2 == 1;
    loop invariant i % 2 == 0 ==> j >= i;
    loop invariant i % 2 == 0 ==> j % 2 == 0;
    loop invariant i % 2 != 0 ==> j % 2 == 1;
    loop invariant b == a * (j - i);
    loop invariant b == a * (j - i) / (j + i);
    loop invariant b == (j - i) * a;;
    loop invariant b == (a * (j - i));
    loop invariant b <= a;
    loop invariant a >= 0 && b >= 0;
    loop invariant a == b ==> flag != 0;
    loop invariant a == b ==> \forall integer k; k >= 0; a == b;
    loop invariant a <= b;
    loop invariant \forall integer k; 0 <= k <= a ==> b == k * (j - i);
    loop invariant \forall integer k; 0 <= k < a ==> (k % 2 == 0 ==> j >= i + 1);
    loop invariant \forall integer k; 0 <= k < a ==> (k % 2 != 0 ==> j >= i);
    loop invariant 1 <= j;
    loop invariant 0; <= j;
    loop invariant 0; <= i;
    loop invariant 0; <= a;
    loop invariant 0 <= b;
    loop invariant (i % 2 == 0) ==> (j % 2 == 0);
    loop invariant (i % 2 == 0) ==> (j % 2 == 0 || j % 2 == 1);;
    loop invariant (i % 2 != 0) ==> (j % 2 == 1);
    loop invariant (i % 2 != 0) ==> (j % 2 != 0);
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
