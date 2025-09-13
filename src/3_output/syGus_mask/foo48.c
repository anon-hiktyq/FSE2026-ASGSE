
/*@
    requires n > 0;
    */
    
void foo48(int n) {

    int c = 0;

    /*@
        loop invariant (n > 0) ==> (((c == 0) && (n == \at(n,Pre))) || (0 <= c <= n));
        loop invariant (\at(n,Pre) > 0) ==> (n == \at(n,Pre));
        loop assigns c;
    */
    while (unknown()) {
        {
            if (unknown()) {
                if (c != n) {
                    c = c + 1;
                }
            } else {
                if (c == n) {
                    c = 1;
                }
            }
        }
    }
}
