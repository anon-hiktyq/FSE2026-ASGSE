
/*@
requires a < 1000000;
requires 0 <= b && b <= 1000000;
*/
void foo008(int a, int b) {

    int res, cnt;
    res = a;
    cnt = b;
    

    /*@
    loop invariant cnt == b - (res - a);
    loop invariant b - cnt <= b;
    loop invariant b - cnt <= b || a + (b - cnt) <= res;
    loop invariant b - cnt < b;
    loop invariant a + cnt == res - b + cnt;
    loop invariant a + (b - cnt) <= res;
    loop invariant a + (b - cnt) < res;
    loop invariant \forall integer k; a <= k <= res ==> k <= a + b;
    loop invariant \forall integer k; 0 <= k <= b ==> res >= a + k;
    loop invariant \forall integer k; 0 <= k <= b ==> a + k <= res;
    loop invariant \forall integer k; 0 <= k <= b - cnt ==> res >= a + k;
    loop invariant \forall integer k; 0 <= k < b ==> a + b == res + cnt - 1;
    loop invariant \forall integer k; 0 <= k < b - cnt ==> res == a + k + 1;
    ```c;
    ```;
    loop invariant res == a + (b - cnt);
    loop invariant res <= a + b;
    loop invariant res - a == b - cnt;
    loop invariant cnt >= 0 && cnt <= b;
    loop invariant cnt <= b;
    loop invariant a <= res;
    loop invariant a + b == res + cnt;
    loop invariant a + b - res == cnt;
    loop invariant \exists integer k; 0 <= k <= b && res == a + k;
    loop invariant 0 <= cnt;
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
