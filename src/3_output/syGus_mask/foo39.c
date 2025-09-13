
/*@
    requires n > 0;
*/
void foo39(int n) {

    int c = 0;

    /*@
        loop invariant (\at(n, Pre) > 0) ==> (((c == 0) && (n == \at(n, Pre))) || ((1 <= c) && (c <= n)));
        loop invariant (\at(n, Pre) > 0) ==> (n == \at(n, Pre));
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
