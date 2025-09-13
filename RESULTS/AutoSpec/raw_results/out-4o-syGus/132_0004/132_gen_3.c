void foo(int j, int c, int t) {
    int i = 0;
    
    /*@
    loop invariant i >= 0;
    loop invariant c > 48 ==> t == c - 48;
    loop invariant j == 2*i || j == i + i;
    loop assigns j, t, i;
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
