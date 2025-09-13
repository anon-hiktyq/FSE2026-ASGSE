// hhk2008_true-unreach-call.c

/*@
requires a < 1000000;
requires 0 <= b && b <= 1000000;
*/
int foo(int a, int b) {
    //int a;
    //int b;
    
    int res, cnt;

    res = a;
    cnt = b;
    
    /*@
    loop invariant res == a + (b - cnt);
    loop invariant cnt <= b;
    loop invariant cnt + res == a + b;
    loop invariant a <= res;
    loop invariant 0 <= cnt;
    loop invariant 0 <= cnt && cnt <= b;
    loop invariant 0 <= b && b <= 1000000;
    loop assigns res;
    loop assigns cnt;
    */
    while (cnt > 0) {
    	cnt = cnt - 1;
        res = res + 1;
    }

    // @ assert res == a + b;
    
    return 0;
}
