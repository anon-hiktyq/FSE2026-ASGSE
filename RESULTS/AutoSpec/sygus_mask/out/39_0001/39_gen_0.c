int unknown();

/*@
requires n > 0;
*/
void foo(int n) {
    int c = 0;

    /*@
    loop invariant c >= 0;
    loop invariant c <= n;
    loop invariant c == n ==> (c == 1);
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
