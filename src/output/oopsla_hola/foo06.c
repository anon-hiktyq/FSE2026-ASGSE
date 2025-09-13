
void foo06() {
  int w = 1;
  int z = 0;
  int x = 0;
  int y = 0;

  
  /*@
    loop assigns z, w, x, y;
  */
  while(unknown1()) {
	  
    
            
        /*@
          // Invariant: x is the count of odd w's seen so far,
          // y is the count of even z's seen so far.
        */
            while(unknown2()){
      if(w%2 == 1) x++;
      if(z%2 == 0) y++;
    }
            
    z = x + y;
    w = z + 1;
  }
            

   /*@ assert x == y; */
}
