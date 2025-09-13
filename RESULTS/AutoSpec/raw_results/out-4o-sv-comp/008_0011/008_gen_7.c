
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
    loop invariant res >= a;
    loop invariant cnt >= 0;
    loop invariant 0 <= b - cnt <= b;
    loop invariant a <= res <= a + b;
    loop invariant a + b == res + cnt;
    loop invariant res == a + b - cnt;
    loop invariant res == a + b - cnt;
    loop invariant res == a + (b - cnt);
    loop invariant res <= a + b;
    loop invariant res <= a + b || cnt <= b;
    loop invariant res <= a + b || cnt + a - res <= b;
    loop invariant res <= a + b || b - cnt <= b;
    loop invariant res <= a + b || a <= res;
    loop invariant res - a == b - cnt;
    loop invariant res - a + cnt == b;
    loop invariant cnt >= 0 && cnt <= b;
    loop invariant cnt == b - (res - a);
    loop invariant cnt <= b;
    loop invariant cnt <= b || b - cnt <= b;
    loop invariant cnt <= b || a <= res;
    loop invariant cnt + a - res <= b;
    loop invariant cnt + a - res <= b || cnt <= b;
    loop invariant cnt + a - res <= b || b - cnt <= b;
    loop invariant cnt + a - res <= b || a <= res;
    loop invariant b - cnt == res - a;
    loop invariant b - cnt <= b;
    loop invariant a <= res;
    loop invariant a <= res || b - cnt <= b;
    loop invariant a + b == res + cnt;
    loop invariant a + b - res == cnt;
    loop invariant \forall integer k; res == a + (b - cnt);
    loop invariant \forall integer k; a <= res;
    loop invariant \forall integer k; 0 <= k <= b ==> res >= a;
    loop invariant 0 <= cnt;
    loop invariant 0 <= b - cnt;
    loop invariant 0 <= b - cnt || res <= a + b;
    loop invariant 0 <= b - cnt || cnt <= b;
    loop invariant 0 <= b - cnt || cnt + a - res <= b;
    loop invariant 0 <= b - cnt || b - cnt <= b;
    loop invariant 0 <= b - cnt || a <= res;
    loop assigns res;
    loop assigns cnt;
    */
    while (cnt > 0) {
    	cnt = cnt - 1;
        res = res + 1;
    }

    // @ assert res == a + b;*/
    

}
