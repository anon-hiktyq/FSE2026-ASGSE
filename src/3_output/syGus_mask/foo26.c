
void foo26(int n) {

    int x = n;
    
    /* >>> LOOP INVARIANT TO FILL <<< */
    
    /*@
      loop invariant (\at(n,Pre) > 1) ==> (x > 0 && x <= \at(n, Pre));
      loop invariant (!(\at(n,Pre) > 1)) ==> ((x == \at(n,Pre)) && (n == \at(n,Pre)));
      loop invariant n == \at(n,Pre);
      loop assigns x;
    */
    while (x > 1) {
        x = x - 1;
    }
}
