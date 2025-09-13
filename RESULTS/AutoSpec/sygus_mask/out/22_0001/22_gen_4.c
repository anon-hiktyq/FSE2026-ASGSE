int main()
{
    int x = 1;
    int m = 1;
    int n;

    /*@
    loop invariant 1 <= x <= n;
    loop invariant m == (unknown() ? x - 1 : m);
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
