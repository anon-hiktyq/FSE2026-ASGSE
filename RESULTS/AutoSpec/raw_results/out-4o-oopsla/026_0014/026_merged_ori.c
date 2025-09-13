
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
    loop invariant z == 2*y;
    loop invariant z == 2 * x;
    loop invariant z <= w;
    loop invariant z < w;
    loop invariant y => (y <= x + 1);
    loop invariant y <= x;
    loop invariant y <= x + z;
    loop invariant y <= w;
    loop invariant x => (x <= y + 1);
    loop invariant x == y || x == y + (y - x);
    loop invariant x == y + z % 2;
    loop invariant x <= y;
    loop invariant x <= y || y <= x;
    loop invariant x <= y || x >= y;
    loop invariant x <= y + w;
    loop invariant x - y <= z;
    loop invariant x + y == z;
    loop invariant w == z + x - y;
    loop invariant w == 2*x + 1;
    loop invariant w == 2 * y + 1;
    loop invariant w == 1 + x + y;
    loop invariant w - z == 1;
    loop invariant k <= y => (y;
    loop invariant k <= x => (x;
    loop invariant \forall integer k; 0 <= k;
    loop invariant \forall integer k; (x + y) % 2 == 0;
    loop invariant \forall integer i; 0 <= i <= w ==> z + i >= x;
    loop invariant \exists integer k; y <= k <= x && (w % 2 == 1);
    loop invariant \exists integer k; x == k && y == k;
    loop invariant \exists integer k; x <= k <= y && (z % 2 == 0);
    loop invariant \exists integer k; 0 <= k && z == 2*k;
    loop invariant \exists integer k; 0 <= k && w == 2*k + 1;
    loop invariant \exists integer i; 0 <= i <= z && y + i == x;
    loop invariant 1 <= x + y;
    loop invariant 0 <= z;
    loop invariant 0 <= w;
    loop invariant (z >= 0) ==> (w > 0);
    loop invariant (z % 2 == 0) ==> (y == x || y == x + 1);
    loop invariant (z % 2 == 0) ==> (y <= x);
    loop invariant (x == y) ==> (w == z + 1);
    loop invariant (x % 2 == y % 2);
    loop invariant (w % 2 == 1) ==> (x == y || x == y + 1);
    loop invariant (w % 2 == 1) ==> (x <= y);
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