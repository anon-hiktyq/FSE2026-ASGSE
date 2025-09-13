
int func8(int c) {
    int x = c;
    int y = 0;

    /* >>> LOOP INVARIANT TO FILL <<< */
    
    /*@
      loop invariant (\at(c,Pre) > 0) ==> (y + x == \at(c,Pre));
      loop invariant (\at(c,Pre) > 0) ==> (x >= 0);
      loop invariant (!(\at(c,Pre) > 0)) ==> ((y == 0)&&(x == \at(c,Pre))&&(c == \at(c,Pre)));
      loop invariant c == \at(c,Pre);
      loop invariant y == \at(y, Pre) + (\at(c, Pre) - x); // This invariant tracks y's accumulation
      loop assigns x, y;
      loop variant x;
    */
    while(x > 0) {
        x = x - 1;
        y = y + 1;
    }
    
    /*@ ensures (c > 0) ==> (y == c);
        ensures !(c > 0) ==> (y == 0);
    */
    return y;
}

void goo8() {
    int t = func8(5);
    //@ assert t == 5;
}
