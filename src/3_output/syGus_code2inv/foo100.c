
/*@
    requires n >= 0;
    */
    
void foo100(int n) {

    int x = n;
    int y = 0;
    
    /* >>> LOOP INVARIANT TO FILL <<< */
    
    /*@
      loop invariant (\at(n,Pre) > 0) ==> (y + x == \at(n,Pre));
      loop invariant (\at(n,Pre) > 0) ==> (x >= 0);
      loop invariant (!(\at(n,Pre) > 0)) ==> ((y == 0) && (x == \at(n,Pre)) && (n == \at(n,Pre)));
      loop invariant n == \at(n,Pre);
      loop assigns y, x;
    */
    while (x > 0) {
        y = y + 1;
        x = x - 1;
    }
    
    /*@ assert y == n; */
}
