
void foo35() {
    int c = 0;

    /*@
      loop invariant ((c == 0)) || ((c >= 1 && c <= 40));
      loop assigns c;
    */
    while (unknown()) {
        if (unknown()) {
            if (c != 40) {
                c = c + 1;
            }
        } else {
            if (c == 40) {
                c = 1;
            }
        }
    }
}
