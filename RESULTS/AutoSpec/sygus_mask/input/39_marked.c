int unknown();

/*@
requires n > 0;
*/
/* 2. FUNC CONTRACT */
void foo(int n) {
    int c = 0;

    /* 1. LOOP INVARIANT */
    while (unknown()) {
        if(c == n) {
            c = 1;
        }
        else {
            c = c + 1;
        }
    }


}
