
/*@
    requires n >= 1;
*/
void foo112(int n, int v1, int v2, int v3) {

    int i = 1;
    int sn = 0;

    /*@
        loop invariant (\at(n, Pre) >= 1) ==> ((1 <= \at(n, Pre)) ==> (1 <= i <= n + 1));
        loop invariant (\at(n, Pre) >= 1) ==> ((1 <= \at(n, Pre)) ==> (sn == i - 1));
        loop invariant (\at(n, Pre) >= 1) ==> ((!(1 <= \at(n, Pre))) ==> ((sn == 0) && (i == 1) && (v3 == \at(v3, Pre)) && (v2 == \at(v2, Pre)) && (v1 == \at(v1, Pre)) && (n == \at(n, Pre))));
        loop invariant (\at(n, Pre) >= 1) ==> (v3 == \at(v3, Pre));
        loop invariant (\at(n, Pre) >= 1) ==> (v2 == \at(v2, Pre));
        loop invariant (\at(n, Pre) >= 1) ==> (v1 == \at(v1, Pre));
        loop invariant (\at(n, Pre) >= 1) ==> (n == \at(n, Pre));
        loop assigns i, sn;
    */
    while (i <= n) {
        i = (i + 1);
        sn = (sn + 1);
    }
}
