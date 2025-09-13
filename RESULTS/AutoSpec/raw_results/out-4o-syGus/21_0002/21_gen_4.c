int main()
{
    int x = 1;
    int m = 1;
    int n;

    /*@
    loop invariant x >= m;
    loop invariant m < n || m == x;
    loop invariant \forall integer k; 1 <= k <= x ==> m >= k;
    loop assigns x, m;
    loop invariant m < n || x >= n;
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
