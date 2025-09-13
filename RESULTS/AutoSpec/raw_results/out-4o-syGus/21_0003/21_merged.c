int main()
{
    int x = 1;
    int m = 1;
    int n;

    /*@
    loop invariant m <= x;
    loop invariant m < n || m >= x;
    loop invariant 1 <= x;
    loop invariant 1 <= m;
    loop invariant (x > 1 && n > 1) ==> m < n;
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
       //@ assert m < n;
       ////@ assert m >= 1;
    }
}
