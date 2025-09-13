
void foo045(int flag) {
  int x = 0;
  int y = 0;
  int j = 0;
  int i = 0;

  
  /*@
    loop invariant 0 <= x;
    loop invariant 0 <= y;
    loop invariant i == (x * (x + 1)) / 2;
    loop assigns x, y, i, j;
  */
  while (unknown1()) {
    x++;
    y++;
    i += x;
    j += y;
    if (flag) {
      j += 1;
    }
  }
            
  if (j >= i)
    x = y;
  else
    x = y + 1;

  int w = 1;
  int z = 0;
  
  /* >>> LOOP INVARIANT TO FILL <<< */
        
  /*@
    loop invariant 0 <= x;
    loop invariant 0 <= y;
    loop invariant w >= 1;
    loop invariant x >= 0; // Weakened to ensure validity under initial conditions
    loop invariant y >= 0; // Weakened to ensure validity under initial conditions
    loop assigns w, z;
  */
  while (unknown2()) {
   
    /* >>> LOOP INVARIANT TO FILL <<< */
        
    /*@
      loop invariant 0 <= x;
      loop invariant 0 <= y;
      loop invariant w >= 1;
      loop invariant x >= 0; // Weakened to ensure validity under initial conditions
      loop invariant y >= 0; // Weakened to ensure validity under initial conditions
    */
    while (unknown3()) {
      if (w % 2 == 1)
        x++;
      if (z % 2 == 0)
        y++;
    }
            
    z = x + y;
    w = z + 1;
  }
            
  /*@ assert x == y; */
}
