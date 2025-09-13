void foo(int j, int c, int t) {
    int i = 0;
    
    /*@
    loop invariant c > 48 ==> i % 2 == 0 || (c < 57 && i % 2 == t % 2);
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
    //@ assert i >= 0;
}
