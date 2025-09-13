
/*@
    requires x >= 0 && x <= 10 && y <= 10 && y >= 0;
    */
    
void foo7(int x, int y) {
  
    /*@
      loop invariant (x - \at(x, Pre)) % 10 == 0;
      loop invariant (y - \at(y, Pre)) % 10 == 0;
      loop assigns x, y;
    */
    while (unknown()) {
        x = x + 10;
        y = y + 10;
    }
    
    /*@ assert (x ==20) ==>  (y != 0); */
}
