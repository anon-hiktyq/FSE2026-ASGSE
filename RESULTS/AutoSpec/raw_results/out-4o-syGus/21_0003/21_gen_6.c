int main()
{
    int x = 1;
    int m = 1;
    int n;

    /*@
    loop invariant 1 <= x <= n;
    loop invariant 1 <= m < n;
    loop invariant m <= x;
    loop invariant x <= n;
    loop assigns m;
    loop assigns x;
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
