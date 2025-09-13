int main()
{
    int x = 1;
    int m = 1;
    int n;

    /*@
    loop invariant x <= n;
    loop invariant m == (x > 1 ? max(m, x) : m);
    loop invariant m == (unknown() ? x - 1 : m);
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
