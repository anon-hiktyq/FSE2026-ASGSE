void foo(int j, int c, int t) {
    int i = 0;
    
    /*@
    loop invariant i >= 0;
    loop invariant j >= 0;
    loop invariant t >= 0;
    loop invariant c > 48 ==> (c < 57 ==> (j == 2 * i && t == c - 48 && i == j + t));
    loop assigns i;
    loop assigns j;
    loop assigns t;
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
