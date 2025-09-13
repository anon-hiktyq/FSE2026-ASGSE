/*@
requires n > 0;
*/
void foo(int n) {
    int c = 0;

    /*@
    loop invariant c == 1 ==> \exists integer k; k >= 0 && k < n;
    loop invariant c == 1 ==> \exists integer k; (k == n);
    loop invariant c == 0 || c == n || (c > 0 && c < n);
    loop invariant c <= n;
    loop invariant c != n || (c == n && c == 1);
    loop invariant 0 <= c;
    loop assigns c;
    */
    while (unknown()) {
        if(c == n) {
            c = 1;
        }
        else {
            c = c + 1;
        }
    }


}
