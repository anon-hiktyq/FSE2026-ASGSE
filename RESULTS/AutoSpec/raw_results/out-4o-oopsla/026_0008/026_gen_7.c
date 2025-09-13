
int unknown1();
int unknown2();
int unknown3();


void foo026() {
  int w = 1, z = 0, x = 0, y = 0;
 
  /*@
  loop invariant z == x + y;
  loop invariant z % 2 == 0;
  loop invariant x == y;
  loop invariant w == z + 1;
  loop invariant 1 <= w;
  loop invariant 0 <= x;
  loop invariant 0 <= y;
  loop invariant 0 <= z;
  loop invariant w % 2 == 1;
  loop assigns w, z, x, y;
  */
  while (unknown1()) {
   
    /*@
    loop invariant z == x + y;
    loop invariant z == x + y || z == 0;
    loop invariant z % 2 == 0;
    loop invariant z % 2 == 0 || z % 2 == 1;
    loop invariant x >= 0 && y >= 0;
    loop invariant x == y;
    loop invariant x - y == 0;
    loop invariant w == z + 1;
    loop invariant w == z + 1 || w == 1;
    loop invariant w % 2 == 0 || w % 2 == 1;
    loop invariant 1 <= w;
    loop invariant 0 <= z;
    loop invariant 0 <= y;
    loop invariant 0 <= x;
    loop invariant (z % 2 == 0) || (z % 2 == 1);
    loop invariant (w % 2 == 1) || (w % 2 == 0);
    loop assigns y;
    loop assigns x;
    */
    while (unknown2()) {
      if (w % 2 == 1)
        x++;
      if (z % 2 == 0)
        y++;
    }
   
    /*@
    loop invariant z == x + y;
    loop invariant z % 2 == 0;
    loop invariant x >= 0 && y >= 0;
    loop invariant x == y;
    loop invariant w == z + 1;
    loop invariant w % 2 == 1;
    loop invariant 1 <= w;
    loop invariant 0 <= z;
    loop invariant 0 <= y;
    loop invariant 0 <= x;
    loop invariant (z % 2 == 0) || (z % 2 == 1);
    loop invariant (w % 2 == 1) || (w % 2 == 0);
    loop assigns z;
    loop assigns w;
    */
    while (unknown3()) {
      z = x + y;
      w = z + 1;
    }
  }
  // @ assert x == y;*/
}