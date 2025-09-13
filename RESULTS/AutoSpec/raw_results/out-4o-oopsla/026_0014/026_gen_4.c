
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
    loop invariant \forall integer k; (x + y) % 2 == 0;
    loop invariant x <= y || y <= x;
    loop invariant x == y || x == y + (y - x);
    loop invariant w == 2*x + 1;
    loop invariant z == 2*y;
    loop invariant \exists integer k; x == k && y == k;
    loop invariant w > z;
    loop invariant (x == y) ==> (w == z + 1);
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