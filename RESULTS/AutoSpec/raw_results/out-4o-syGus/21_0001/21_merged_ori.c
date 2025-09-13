int main()
{
    int x = 1;
    int m = 1;
    int n;

    /*@
    loop invariant x > 1 ==> \exists integer k; 1 <= k < x && m == k;
    loop invariant x == m + 1 || x > m;
    loop invariant x <= n;
    loop invariant m < x;
    loop invariant m < n || x >= n;
    loop invariant m < n ==> \exists integer k; 1 <= k < x && unknown();
    loop invariant 1 <= x;
    loop invariant 1 <= m;
    loop assigns x;
    loop assigns n;
    loop assigns m;
    */
    while (x < n) {
        if (unknown()) {
            m = x;
        }
        x = x + 1;
    }

    //post-condition
    if(n > 1) {
       // @ assert m < n;
       //// @ assert m >= 1;
    }
}
