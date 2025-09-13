
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

    /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
      loop invariant a >= 0;
      loop invariant b >= 0;
      loop invariant i >= 0;
      loop invariant flag == \at(flag,Pre);
    */
    while (unknown()) {
        a++;
        b += (j - i);
        i += 2;
        if (i%2 == 0) {
            j += 2;
        } else {
            j++;
        }
    }

    if (flag) {
        /*@ assert a == b;*/
    }
}
