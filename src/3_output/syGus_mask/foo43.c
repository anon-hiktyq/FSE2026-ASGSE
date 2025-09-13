
/*@
    requires n > 0;
    */
void foo43(int n) {

    int c = 0;

    /*@
      loop invariant (n > 0) ==> (((c == 0)&&(n == \at(n,Pre))) || ((c >= 1 && c <= n + 1) || (c > n + 1)));
      loop invariant (\at(n,Pre) > 0) ==> (n == \at(n,Pre));
      loop assigns c;
    */
    while (unknown()) {
        if (unknown()) {
            if (c > n) {
                c = c + 1;
            }
        } else {
            if (c == n) {
                c = 1;
            }
        }
    }
}
