void foo(int j, int c, int t) {
    int i = 0;
    
    /*@
    loop invariant c > 48 ==> j == 2*i;
    loop invariant c > 48 ==> j == 2*i - t;
    loop invariant c > 48 ==> j == 2*i && t >= 0 && t < 9;
    loop invariant c > 48 ==> i % 2 == 0;
    loop invariant c > 48 ==> (c < 57 ==> (j == 2*i && t == c - 48 && i >= j + t));
    loop invariant c > 48 && c < 57 ==> t == c - 48;
    loop invariant c <= 57;
    loop invariant c <= 48 || c >= 57 || j == i + i;
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
