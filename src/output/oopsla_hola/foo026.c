
void foo026() {
  int w = 1, z = 0, x = 0, y = 0;
 
        /* >>> LOOP INVARIANT TO FILL <<< */
        
            /*@
              loop invariant  x >= 0;
              loop invariant  y >= 0;
              loop invariant  w > 0; // Changed from w >= 1 to w > 0 for clarity
              loop invariant  z == x + y;
            */
            while (unknown1()) {
    
        /* >>> LOOP INVARIANT TO FILL <<< */
        
            /*@
              loop invariant \forall int i; 0 <= i <= x ==> (i % 2 == 1 ==> w % 2 == 1) && (i % 2 == 0 ==> z % 2 == 0);
            */
            while (unknown2()) {
      if (w % 2 == 1)
        x++;
      if (z % 2 == 0)
        y++;
    }
            
   
        /* >>> LOOP INVARIANT TO FILL <<< */
        
            /*@
              w > 0 && z == x + y; // Changed from w >= 1 to w > 0 for clarity
            */
            while (unknown3()) {
      z = x + y;
      w = z + 1;
    }
            
  }
            
  /*@ assert x == y;*/
}
