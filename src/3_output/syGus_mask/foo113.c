
/*@
    requires n >= 1;
    ensures \at(sn, Post) == n;
*/
void foo113(int n, int v1, int v2, int v3) {

    int i = 1;
    int sn = 0;

    /*@
        loop invariant 1 <= i <= n + 1;
        loop invariant sn == i - 1;
        loop invariant n >= 1;
        loop invariant v1 == \at(v1, Pre);
        loop invariant v2 == \at(v2, Pre);
        loop invariant v3 == \at(v3, Pre);
        loop invariant n == \at(n, Pre);
        loop assigns i, sn;
    */
    while (i <= n) {
        i = i + 1;
        sn = sn + 1;
    }
}
