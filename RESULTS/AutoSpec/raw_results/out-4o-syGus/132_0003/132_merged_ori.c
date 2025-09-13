void foo(int j, int c, int t) {
    int i = 0;
    
    /*@
    loop invariant t == c - 48 || (c <= 48 || c >= 57) ==> t == 0;
    loop invariant j == 2 * (i / 2);
    loop invariant j == 2 * (i - t);
    loop invariant c > 48 ==> t == c - 48;
    loop invariant c > 48 ==> j == 2*i;
    loop invariant c > 48 ==> j == 2*i - 48;
    loop invariant c > 48 ==> i >= 2 * (c - 48);
    loop invariant c > 48 ==> i == 2*j + c - 48;
    loop invariant c > 48 ==> i == 2 * i + c - 48;
    loop invariant c > 48 ==> i % 2 == 0;
    loop invariant c > 48 ==> c < 57 ==> i == 2 * (i / 2) + (c - 48);
    loop invariant c > 48 && c < 57 ==> t == c - 48;
    loop invariant c <= 48 || c >= 57 ==> j == i;
    loop invariant 0 <= j;
    loop invariant 0 <= i;
    loop assigns t;
    loop assigns j;
    loop assigns i;
    */
    while(unknown()) {
        if(c > 48) {
            if (c < 57) {
                j = i + i;
                t = c - 48;
                i = j + t;
            }
        }
    } 

    //post-condition
    // @ assert i >= 0;
}
