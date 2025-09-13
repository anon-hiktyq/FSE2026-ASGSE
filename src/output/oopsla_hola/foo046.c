
void foo046() {

  int w = 1;
  int z = 0;
  int x = 0;
  int y = 0;

  
            
        /* >>> LOOP INVARIANT TO FILL <<< */
        
            /*@
            loop invariant w >= 1; // w is always at least 1
            loop invariant z == y; // z tracks the number of increments of y
            loop invariant y <= z; // y cannot exceed z
            loop assigns w, z, x, y;
            */
            while (unknown()) {
    if (w % 2 == 1) {
      x++;
      w++;
    }
    if (z % 2 == 0) {
      y++;
      z++;
    }
  }
            

  /*@ assert x <= 1; */

}
