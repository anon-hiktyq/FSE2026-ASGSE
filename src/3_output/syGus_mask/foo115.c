
void foo115() {

    int sn = 0;
    int x = 0;
    
    /*@
      requires x == 0 && sn == 0;
    */
    /*@
      loop invariant sn == x;
      loop invariant sn >= 0 && x >= 0;
      loop assigns x, sn;
    */
    while (unknown()) {
      x = (x + 1);
      sn = (sn + 1);
    }
}
