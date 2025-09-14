
void foo60(int flag) {
    unsigned int i,j,a,b;
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
        loop invariant b == a * (j - i) + \at(b, Pre);
        loop invariant i == 2 * a + \at(i, Pre);
        loop invariant j >= 1 + a;
        loop invariant flag == \at(flag, Pre);
        loop assigns a, b, i, j;
        loop variant a; // Using a simple integer variant
    */
    while (unknown()) {
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
        /*@ assert a == b;*/
    }
}
