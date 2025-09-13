int main()
{
    int x = 1;
    int m = 1;
    int n;

    /*@
    loop invariant x >= m;
    loop invariant m <= n;
    loop invariant \forall integer k; 1 <= k <= x ==> (k < n || x >= n); 
    loop invariant n >= 1; 
    loop invariant m == 1 || x > 1;
    loop assigns m, x, n;
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
