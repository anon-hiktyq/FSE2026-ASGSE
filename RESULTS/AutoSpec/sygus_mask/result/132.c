void foo(int j, int c, int t) {
    int i = 0;
    
    /*@
    loop invariant t == c - 48 ==> (c > 48 && c < 57);
    loop invariant j == 2*i || (c <= 48 || c >= 57);
    loop invariant j == 2 * i;
    loop invariant j == 2 * i || j == 0;
    loop invariant 0 <= i;
    loop assigns t;
    loop assigns j;
    loop assigns i;
    loop assigns c;
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
    //@assert(i >= 0);
}