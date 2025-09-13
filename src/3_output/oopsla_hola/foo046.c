
int unknown();


void foo046() {

  int w = 1;
  int z = 0;
  int x = 0;
  int y = 0;


  
            
        /* >>> LOOP INVARIANT TO FILL <<< */
        
            /*@
          PLACE_HOLDER_FOR_LOOP
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