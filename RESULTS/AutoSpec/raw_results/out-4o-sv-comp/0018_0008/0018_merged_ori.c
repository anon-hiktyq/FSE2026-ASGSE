
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
    loop invariant j; <= a + i;
    loop invariant j; < a + i;
    loop invariant j <= i;
    loop invariant j <= i || j <= a + i;
    loop invariant j <= i || i <= j;
    loop invariant j <= i || i <= j;
    loop invariant j <= i || b <= a;
    loop invariant j <= i || 1 <= j;
    loop invariant j <= i || 0 <= i;
    loop invariant j <= i || 0 <= b;
    loop invariant j <= i || 0 <= b;
    loop invariant j <= i || 0 <= a;
    loop invariant j <= a + i || i <= j;
    loop invariant j <= a + i || 1 <= j;
    loop invariant j < i;
    loop invariant i; <= j;
    loop invariant i; < j;
    loop invariant i; < j;
    loop invariant i; < j;
    loop invariant i; < j;
    loop invariant i; < j;
    loop invariant i; < j;
    loop invariant i; < j;
    loop invariant i >= 0 && j >= 1;;
    loop invariant i >= 0 && j >= 1;
    loop invariant i <= j;
    loop invariant i <= j || j <= a + i;
    loop invariant i <= j || i <= j;
    loop invariant i <= j || 1 <= j;
    loop invariant i <= j || 0 <= a;
    loop invariant i < j;
    loop invariant i % 2 == 1 || j % 2 == 0;
    loop invariant i % 2 == 1 ==> j % 2 == 1;
    loop invariant i % 2 == 0 || j % 2 == 1;
    loop invariant i % 2 == 0 ==> j % 2 == 0;;
    loop invariant i % 2 == 0 ==> j % 2 == 0;
    loop invariant i % 2 == 0 ==> (j % 2 == 0);;
    loop invariant i % 2 == (j - a) % 2;;
    loop invariant i % 2 != 0 ==> j % 2 == 1;
    loop invariant i % 2 != 0 ==> j % 2 != 0;;
    loop invariant i % 2 != 0 ==> (j % 2 != 0);;
    loop invariant b; <= a;
    loop invariant b; < a;
    loop invariant b == a * (j - i);
    loop invariant b == a * (j - i) / i + (flag ? 0 : 1);;
    loop invariant b == a * (j - i) / (j - i + 1);;
    loop invariant b == a * (j - i) / (j - i != 0 ? j - i : 1);;
    loop invariant b == a * (j - i + 1) / 2;
    loop invariant b == (i / 2) * ((j - i) + (j % 2));;
    loop invariant b == (a * (j - i)) / (j != i ? j - i : 1);
    loop invariant b <= a || j <= a + i;
    loop invariant b <= a || i <= j;
    loop invariant b <= a || i <= j;
    loop invariant b <= a || 1 <= j;
    loop invariant b <= a || 0 <= i;
    loop invariant b <= a || 0 <= b;
    loop invariant b <= a || 0 <= b;
    loop invariant b <= a || 0 <= a;
    loop invariant a >= b || b >= a;
    loop invariant a == 0 || b != 0;
    loop invariant \forall integer k; 0 <= k < a ==> i >= 2 * k;
    loop invariant \forall integer k; 0 <= k < a ==> (b == (k * (j - i)));
    loop invariant 1; <= j;
    loop invariant 1; < j;
    loop invariant 1 <= j;
    loop invariant 1 <= j || j <= i;
    loop invariant 1 <= j || j <= a + i;
    loop invariant 1 <= j || i <= j;
    loop invariant 1 <= j || i <= j;
    loop invariant 1 <= j || i <= j;
    loop invariant 1 <= j || b <= a;
    loop invariant 1 <= j || 1 <= j;
    loop invariant 1 <= j || 0 <= j;
    loop invariant 1 <= j || 0 <= i;
    loop invariant 1 <= j || 0 <= b;
    loop invariant 1 <= j || 0 <= b;
    loop invariant 1 <= j || 0 <= a;
    loop invariant 1 < j;
    loop invariant 0; <= i;
    loop invariant 0; <= b;
    loop invariant 0; <= a;
    loop invariant 0; < i;
    loop invariant 0; < b;
    loop invariant 0; < a;
    loop invariant 0 <= j;
    loop invariant 0 <= j || j <= i;
    loop invariant 0 <= j || j <= a + i;
    loop invariant 0 <= j || i <= j;
    loop invariant 0 <= j || i <= j;
    loop invariant 0 <= j || b <= a;
    loop invariant 0 <= j || 1 <= j;
    loop invariant 0 <= j || 0 <= i;
    loop invariant 0 <= j || 0 <= b;
    loop invariant 0 <= j || 0 <= b;
    loop invariant 0 <= j || 0 <= a;
    loop invariant 0 <= i || j <= a + i;
    loop invariant 0 <= i || i <= j;
    loop invariant 0 <= i || i <= j;
    loop invariant 0 <= i || 1 <= j;
    loop invariant 0 <= i || 0 <= b;
    loop invariant 0 <= i || 0 <= b;
    loop invariant 0 <= i || 0 <= a;
    loop invariant 0 <= b;
    loop invariant 0 <= b || j <= a + i;
    loop invariant 0 <= b || j <= a + i;
    loop invariant 0 <= b || i <= j;
    loop invariant 0 <= b || i <= j;
    loop invariant 0 <= b || i <= j;
    loop invariant 0 <= b || i <= j;
    loop invariant 0 <= b || 1 <= j;
    loop invariant 0 <= b || 1 <= j;
    loop invariant 0 <= b || 0 <= b;
    loop invariant 0 <= b || 0 <= a;
    loop invariant 0 <= b || 0 <= a;
    loop invariant 0 <= a || j <= a + i;
    loop invariant 0 <= a || i <= j;
    loop invariant 0 <= a || 1 <= j;
    loop invariant 0 <= a && 0 <= b;;
    loop invariant 0 < j;
    loop invariant 0 < b;
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
