
/*@
    requires n > 0;
    ensures \true; // Placeholder for any post-condition you might want to verify
    */
void foo38(int n) {

    int c = 0;

    /*@
        loop invariant (n > 0) ==> (((c == 0) && (n == \at(n,Pre))) || (0 <= c <= n));
        loop invariant (\at(n,Pre) > 0) ==> (n == \at(n,Pre));
        loop assigns c;
    */
    while (unknown()) {
        if (c == n) {
            c = 1;
        } else {
            c = c + 1;
        }
    }
}
