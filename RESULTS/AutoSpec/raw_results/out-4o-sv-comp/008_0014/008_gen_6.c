
/*@
requires a < 1000000;
requires 0 <= b && b <= 1000000;
*/
void foo008(int a, int b) {

    int res, cnt;
    res = a;
    cnt = b;
    

    /*@
    loop invariant res == a + (b - cnt);
    loop invariant cnt >= 0 && cnt <= b;
    loop invariant res >= a;
    loop invariant b - cnt == res - a;
    loop invariant cnt == b - (res - a);
    loop invariant cnt + (res - a) == b;
    loop invariant 0 <= b - cnt;
    loop invariant res <= a + b;
    loop invariant res == a + (b - cnt);
    loop invariant res <= a + b;
    loop invariant res - a == b - cnt;
    loop invariant cnt >= 0 && cnt <= b;
    loop invariant cnt == b - (res - a);
    loop invariant cnt <= b;
    loop invariant cnt + (res - a) == b;
    loop invariant b - cnt == res - a;
    loop invariant b - cnt <= b;
    loop invariant a <= res;
    loop invariant a + b - cnt == res;
    loop invariant 0 <= cnt;
    loop invariant 0 <= cnt && cnt <= b;
    loop invariant 0 <= b - cnt;
    loop assigns res;
    loop assigns cnt;
    */
    while (cnt > 0) {
    	cnt = cnt - 1;
        res = res + 1;
    }

    // @ assert res == a + b;*/
    

}
