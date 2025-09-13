void foo(int j, int c, int t) {
    int i = 0;
    
    /*@
    loop invariant t == c - 48 ==> c > 48 && c < 57;
    loop invariant t == c - 48 ==> 48 < c < 57;
    loop invariant t == c - 48 ==> (c > 48 && c < 57);
    loop invariant t == c - 48 && c > 48 && c < 57 ==> j == 2*i + (c - 48);
    loop invariant j == 2*i;
    loop invariant j == 2*i || j == 0;;
    loop invariant j == 2*i || j == 0;
    loop invariant j == 2*i || (c <= 48 || c >= 57);
    loop invariant j == 2 * i;
    loop invariant j == 2 * i || j == 0;
    loop invariant c > 48 ==> (c < 57 ==> t == c - 48);
    loop invariant \forall integer k; k < i ==> (c > 48 ==> (c < 57 ==> j == 2*k && t == c - 48));
    loop invariant 0 <= t;
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


}
