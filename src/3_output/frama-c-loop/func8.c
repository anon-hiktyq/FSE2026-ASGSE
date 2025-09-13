
int func8(int c) {
    int x = c;
    int y = 0;

    /* >>> LOOP INVARIANT TO FILL <<< */
    
    /*@
      loop invariant (\at(c,Pre) > 0) ==> (y + x == \at(c,Pre));
      loop invariant (\at(c,Pre) > 0) ==> (x >= 0);
      loop invariant (!(\at(c,Pre) > 0)) ==> ((y == 0)&&(x == \at(c,Pre))&&(c == \at(c,Pre)));
      loop invariant c == \at(c,Pre);
      loop assigns x, y;
    */
    while(x > 0) {
        x = x - 1;
        y = y + 1;
    }
    
    return y;
}
