
void foo25() {
    int x = 10000;
    
    /*@
      loop invariant x >= 0; // x is always non-negative
      loop invariant x + 0 == 10000 - (10000 - x); // x decreases from 10000 to 0
      loop assigns x; // x is the only variable being modified in the loop
    */
    while (x > 0) {
        x = x - 1;
    }
    
    /*@ assert x == 0; */
}
