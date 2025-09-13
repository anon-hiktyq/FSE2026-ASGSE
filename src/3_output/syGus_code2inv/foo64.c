
void foo64(int y) {
    int x = 1;
    
    /*@
      loop invariant (1 <= x) && (x <= 11); // x ranges from 1 to 10, inclusive
      loop invariant ((x == 1) && (y == \at(y, Pre))) || (y == 10 - (x - 1)); // y is always 10 minus (x - 1)
      loop assigns y, x;
    */
    /*@
      PLACE_HOLDER_FOR_LOOP
    */
    while (x <= 10) {
        y = 10 - x;
        x = x + 1;
    }

    /*@ assert (y < 10); */
}
