int main()
{
    int x = 1;
    int m = 1;
    int n;

    /*@
    loop invariant x >= 1;
    loop invariant x <= n;
    loop invariant m >= 1;
    loop invariant m < x;
    loop assigns x;
    loop assigns m;
    loop assigns n;
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
