int main()
{
    int x = 1;
    int m = 1;
    int n;

    /*@
    loop invariant x <= n;
    loop invariant m == \max(1, \exists integer k; 1 <= k < x && unknown() ? k : m);
    loop invariant m == 1 || (m == x && unknown());
    loop invariant m == (unknown() ? x - 1 : m);
    loop invariant m <= x;
    loop invariant 1 <= x;
    loop assigns x;
    loop assigns m;
    */
    while (x < n) {
        if (unknown()) {
            m = x;
        }
        x = x + 1;
    }


}
