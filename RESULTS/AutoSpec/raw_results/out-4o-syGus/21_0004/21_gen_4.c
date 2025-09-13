int main()
{
    int x = 1;
    int m = 1;
    int n;

    /*@
    loop invariant 1 <= x <= n;
    loop invariant m >= 1;
    loop invariant x > m || m == \old(m);
    loop invariant m < n || x >= n;
    loop assigns x, m;
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
