void foo(int j, int c, int t) {
    int i = 0;
    
    /*@
    loop invariant 0 <= i;
    loop invariant \forall integer k; k < i ==> (c > 48 ==> (c < 57 ==> j == 2*k && t == c - 48));
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


}
