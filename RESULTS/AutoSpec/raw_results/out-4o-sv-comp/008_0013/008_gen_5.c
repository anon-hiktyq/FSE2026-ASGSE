
/*@
requires a < 1000000;
requires 0 <= b && b <= 1000000;
*/
void foo008(int a, int b) {

    int res, cnt;
    res = a;
    cnt = b;
    

    /*@
    loop invariant res - a == b - cnt;
    loop invariant a + b >= res;
    loop invariant cnt >= 0;
    loop invariant cnt + (res - a) == b;
    loop invariant \forall integer k; 0 <= k <= b - cnt ==> res == a + k;
    loop invariant res == a + (b - cnt);
    loop invariant cnt <= b;
    loop invariant 0 <= cnt;
    loop invariant 0 <= cnt && cnt <= b;
    loop assigns res;
    loop assigns cnt;
    */
    while (cnt > 0) {
    	cnt = cnt - 1;
        res = res + 1;
    }

    // @ assert res == a + b;*/
    

}
