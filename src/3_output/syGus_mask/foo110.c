
/*@
    requires n >= 1;
*/
void foo110(int n) {

    int i = 1;
    int sn = 0;

    /*@
        loop invariant (\at(n,Pre) >= 1) ==> ((1 <= \at(n,Pre)) ==> (1 <= i <= n + 1));
        loop invariant (\at(n,Pre) >= 1) ==> ((1 <= \at(n,Pre)) ==> (sn == i - 1));
        loop invariant (\at(n,Pre) >= 1) ==> ((!(1 <= \at(n,Pre))) ==> ((sn == 0) && (i == 1) && (n == \at(n,Pre))));
        loop invariant (\at(n,Pre) >= 1) ==> (n == \at(n,Pre));
        loop assigns i, sn;
    */
    while (i <= n) {
        i = i + 1;
        sn = sn + 1;
    }
}
