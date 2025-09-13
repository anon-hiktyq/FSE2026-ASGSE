
int unknown1();
int unknown2();
int unknown3();


void foo026() {
  int w = 1, z = 0, x = 0, y = 0;
 
  /*@
  loop invariant z == x + y || z + 1 == w;
  loop invariant z % 2 == 0;
  loop invariant z % 2 == 0 || z % 2 == 1;
  loop invariant x == y;
  loop invariant w == z + 1;
  loop invariant w % 2 == 1;
  loop invariant w % 2 == 0 || w % 2 == 1;
  loop invariant \forall integer i; 0 <= i < x+y ==> (w % 2 == 1) && (z % 2 == 0);
  loop invariant 1 <= w;
  loop invariant 0 <= z;
  loop invariant 0 <= y;
  loop invariant 0 <= x;
  loop invariant (w % 2 == 1) ==> x >= y;
  loop invariant (w % 2 == 1) ==> (z % 2 == 0);
  loop invariant (w % 2 == 0) ==> y >= x;
  loop invariant (w % 2 == 0) ==> (z % 2 == 1);
  loop assigns z;
  loop assigns y;
  loop assigns x;
  loop assigns w;
  */
  while (unknown1()) {
   
    /*@
    loop invariant z == x + y;
    loop invariant z == x + y || z == x + y + 1;
    loop invariant z < w;
    loop invariant z % 2 == 1 || z % 2 == 0;
    loop invariant z % 2 == 0;
    loop invariant y == x || y == x + 1;
    loop invariant y <= z;
    loop invariant y - x == 0 || y - x == 1;
    loop invariant y - x <= 1;
    loop invariant x >= 0 && y >= 0;
    loop invariant x <= z;
    loop invariant x <= y;
    loop invariant x <= y + 1;
    loop invariant x + y == z || x + y + 1 == w;
    loop invariant x + y <= z;
    loop invariant x + y <= z + w;
    loop invariant x + y <= w - 1;
    loop invariant w - z == 1;
    loop invariant w % 2 == 1 || w % 2 == 0;
    loop invariant \forall integer i; 0 <= i <= z ==> (w % 2 == 1 && z % 2 == 0) || (z % 2 == 1 && w % 2 == 0);
    loop invariant \forall integer i; 0 <= i <= x ==> (w % 2 == 1) && (z % 2 == 0);
    loop invariant \forall integer i; 0 <= i < y ==> (w % 2 == 1) && (z % 2 == 0);
    loop invariant \forall integer i; 0 <= i < x+y+z ==> w == z + 1;
    loop invariant 2 * z == w + w - 2;
    loop invariant 0 <= y - x;
    loop invariant (z % 2 == 0);
    loop invariant (w % 2 == 1);
    loop invariant z == x + y || z + 1 == w;
    loop invariant z % 2 == 0 || z % 2 == 1;
    loop invariant x == y;
    loop invariant w == z + 1;
    loop invariant w % 2 == 1;
    loop invariant w % 2 == 0 || w % 2 == 1;
    loop invariant \forall integer i; 0 <= i < x+y ==> (w % 2 == 1) && (z % 2 == 0);
    loop invariant 1 <= w;
    loop invariant 0 <= z;
    loop invariant 0 <= y;
    loop invariant 0 <= x;
    loop invariant (w % 2 == 1) ==> x >= y;
    loop invariant (w % 2 == 1) ==> (z % 2 == 0);
    loop invariant (w % 2 == 0) ==> y >= x;
    loop invariant (w % 2 == 0) ==> (z % 2 == 1);
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
    loop invariant z == x + y || z + 1 == w;
    loop invariant z % 2 == 0;
    loop invariant z % 2 == 0 || z % 2 == 1;
    loop invariant y - x <= 1;
    loop invariant x == y;
    loop invariant x <= y;
    loop invariant w == z + 1;
    loop invariant w % 2 == 1;
    loop invariant w % 2 == 0 || w % 2 == 1;
    loop invariant \forall integer i; 0 <= i < x+y ==> (w % 2 == 1) && (z % 2 == 0);
    loop invariant 1 <= w;
    loop invariant 0 <= z;
    loop invariant 0 <= y;
    loop invariant 0 <= y - x;
    loop invariant 0 <= x;
    loop invariant (w % 2 == 1) ==> x >= y;
    loop invariant (w % 2 == 1) ==> (z % 2 == 0);
    loop invariant (w % 2 == 0) ==> y >= x;
    loop invariant (w % 2 == 0) ==> (z % 2 == 1);
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