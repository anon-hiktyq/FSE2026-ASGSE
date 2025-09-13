
/*@
requires a < 1000000;
requires 0 <= b && b <= 1000000;
*/
void foo008(int a, int b) {

    int res, cnt;
    res = a;
    cnt = b;
    

    /*@
    loop invariant res - a + cnt == b;
    loop invariant cnt <= b || a <= res;
    loop invariant cnt <= b || 0 <= cnt;
    loop invariant cnt <= b || (a + cnt) <= res;
    loop invariant b - cnt <= b;
    loop invariant b - cnt <= b || cnt <= b;
    loop invariant b - cnt <= b || a <= res;
    loop invariant b - cnt <= b || a < res;
    loop invariant b - cnt <= b || 0 <= cnt;
    loop invariant b - cnt <= b || (a + cnt) <= res;
    loop invariant a <= res || 0 <= cnt;
    loop invariant a <= res || (a + cnt) <= res;
    loop invariant a < res || cnt <= b;
    loop invariant a < res || a <= res;
    loop invariant a < res || 0 <= cnt;
    loop invariant a + b == res + cnt;
    loop invariant a + b - cnt == res;
    loop invariant (a + cnt) <= res;
    loop invariant (a + cnt) <= res || 0 <= cnt;
    loop invariant (a + b) - cnt == res;
    loop invariant res == a + b - cnt;
    loop invariant res == a + (b - cnt);
    loop invariant res <= a + b;
    loop invariant res - a == b - cnt;
    loop invariant cnt == b - (res - a);
    loop invariant cnt <= b;
    loop invariant cnt <= b && cnt >= 0;
    loop invariant cnt + res == a + b;
    loop invariant a <= res;
    loop invariant 0 <= cnt;
    loop invariant (a + b) - res == cnt;
    loop assigns res;
    loop assigns cnt;
    */
    while (cnt > 0) {
    	cnt = cnt - 1;
        res = res + 1;
    }

    // @ assert res == a + b;*/
    

}
