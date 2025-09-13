
/*@
requires a < 1000000;
requires 0 <= b && b <= 1000000;
*/
void foo008(int a, int b) {

    int res, cnt;
    res = a;
    cnt = b;
    

    /*@
    loop invariant 0 <= cnt <= b;
    loop invariant res == a + b - cnt;
    loop invariant res <= a + b;
    loop invariant a <= res;
    loop assigns cnt, res;
    loop invariant res == a + b - cnt;
    loop invariant res == a + (b - cnt);
    loop invariant res <= a + b;
    loop invariant res - a + cnt == b;
    loop invariant cnt >= 0 && cnt <= b;
    loop invariant cnt == b - (res - a);
    loop invariant cnt <= b;
    loop invariant b - cnt == res - a;
    loop invariant a <= res;
    loop invariant a + b - res == cnt;
    loop invariant \forall integer k; a <= res;
    loop invariant 0 <= cnt;
    loop assigns res;
    loop assigns cnt;
    */
    while (cnt > 0) {
    	cnt = cnt - 1;
        res = res + 1;
    }

    // @ assert res == a + b;*/
    

}
