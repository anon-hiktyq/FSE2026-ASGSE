int main()
{
    int x = 1;
    int m = 1;
    int n;

    /*@
    loop invariant 1 <= x <= n;
    loop invariant m < n;
    loop invariant m >= 1;
    loop invariant \exists integer k; 1 <= k < x && (unknown() ==> m == k);
    loop assigns x;
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
