
int unknown1();
int unknown2();
int unknown3();


void foo026() {
  int w = 1, z = 0, x = 0, y = 0;
 
  /*@
  loop invariant z % 2 == 0;
  loop invariant x >= 0 && y >= 0;
  loop invariant x == y;
  loop invariant w == z + 1;
  loop invariant w % 2 == 1;
  loop invariant 1 <= w;
  loop invariant 0 <= z;
  loop invariant 0 <= y;
  loop invariant 0 <= x;
  loop invariant (z % 2 == 0);
  loop invariant (z % 2 == 0) || (z % 2 == 1);
  loop invariant (w % 2 == 1) || (w % 2 == 0);
  loop assigns z;
  loop assigns y;
  loop assigns x;
  loop assigns w;
  */
  while (unknown1()) {
   
    /*@
    loop invariant z % 2 == 0;;
    loop invariant y <= x;
    loop invariant x >= 0 && y >= 0;;
    loop invariant x == y;;
    loop invariant x % 2 == y % 2;
    loop invariant w == z + 1;;
    loop invariant w + z == 2*x + 1;
    loop invariant w % 2 == 1;;
    loop invariant w % 2 == 1;
    loop invariant \forall integer k; 0 <= k < z ==> (z % 2 == 0 || z % 2 == 1);
    loop invariant \forall integer k; 0 <= k < y ==> x == y;
    loop invariant 1 <= w;;
    loop invariant 0 <= z;;
    loop invariant 0 <= y;;
    loop invariant 0 <= x;;
    loop invariant (z % 2 == 0) || (z % 2 == 1);;
    loop invariant (w % 2 == 1) || (w % 2 == 0);;
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