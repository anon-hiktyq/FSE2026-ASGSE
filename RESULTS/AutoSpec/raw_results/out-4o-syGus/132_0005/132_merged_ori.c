void foo(int j, int c, int t) {
    int i = 0;
    
    /*@
    loop invariant t == c - 48 || t == 0;
    loop invariant j == 2 * i;
    loop invariant j == 2 * ((i - t) / 2);
    loop invariant c > 48 ==> t == c - 48;
    loop invariant c > 48 ==> i % 2 == 0;
    loop invariant c > 48 ==> i % 2 == 0 || (c < 57 && i % 2 == t % 2);
    loop invariant c == 48 || c >= 57 || i == j + t;
    loop invariant c <= 57;
    loop invariant 0 <= t;
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
