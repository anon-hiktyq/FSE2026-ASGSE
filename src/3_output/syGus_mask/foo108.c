
/*@
    requires a <= m;
*/
void foo108(int m, int j, int a, int c) {

    int k = 0;

    /*@
        loop invariant 0 <= k;
        loop invariant m >= a;
        loop invariant m >= \at(m, Pre);
        loop assigns k, m;
    */
    while (k < c) {

        if (m < a) {
            m = a;
        }

        k = k + 1;
    }
}
