
int unknown1();
int unknown2();
int unknown3();


void foo026() {
  int w = 1, z = 0, x = 0, y = 0;
 
  /*@
  loop invariant x == y;
  loop invariant w == z + 1;
  loop invariant w % 2 == 1;
  loop invariant 1 <= w;
  loop invariant 0 <= y;
  loop invariant 0 <= x;
  loop invariant (z % 2 == 0) ==> (y >= x);
  loop invariant (w % 2 == 1) ==> (x >= y);
  loop assigns z;
  loop assigns y;
  loop assigns x;
  loop assigns w;
  */
  while (unknown1()) {
   
    /*@
    loop invariant w == 1 + x + y;
    loop invariant x + y == z;
    loop invariant (z % 2 == 0) ==> (y == x || y == x + 1);
    loop invariant (w % 2 == 1) ==> (x == y || x == y + 1);
    loop invariant 1 <= x + y;
    loop invariant w >= 1;
    loop invariant \forall integer k; 0 <= k <= x => (x <= y + 1);
    loop invariant \forall integer k; 0 <= k <= y => (y <= x + 1);
    loop invariant x == y;
    loop invariant w == z + 1;
    loop invariant w % 2 == 1;
    loop invariant 1 <= w;
    loop invariant 0 <= y;
    loop invariant 0 <= x;
    loop invariant (z % 2 == 0) ==> (y >= x);
    loop invariant (w % 2 == 1) ==> (x >= y);
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
    loop invariant x == y;
    loop invariant w == z + 1;
    loop invariant w % 2 == 1;
    loop invariant 1 <= w;
    loop invariant 0 <= y;
    loop invariant 0 <= x;
    loop invariant (z % 2 == 0) ==> (y >= x);
    loop invariant (w % 2 == 1) ==> (x >= y);
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