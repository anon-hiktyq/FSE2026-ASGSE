
void foo121() {
    int i = 1;
    int sn = 0;

    /*@
        loop invariant i >= 1 && i <= 9;
        loop invariant sn >= 0 && sn <= 8;
        loop invariant sn == i - 1;
        loop assigns i, sn;
    */
    while (i <= 8) {
        i = (i + 1);
        sn = (sn + 1);
    }
}
