
void foo132(int j, int c, int t) {

    int i = 0;

    /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
      loop invariant ((i == 0) && (t == \at(t, Pre)) && (c == \at(c, Pre)) && (j == \at(j, Pre))) || (t == c - 48);
      loop invariant ((i == 0) && (t == \at(t, Pre)) && (c == \at(c, Pre)) && (j == \at(j, Pre))) || (i == j + t);
      loop invariant c == \at(c, Pre);
      loop assigns i, j, t;
    */
    while(unknown()) {
        if (c > 48) {
            if (c < 57) {
                j = i + i;
                t = c - 48;
                i = j + t;
            }
        }
    }
}
