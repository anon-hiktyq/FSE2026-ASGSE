
int unknown();


void foo046() {

  int w = 1;
  int z = 0;
  int x = 0;
  int y = 0;


  /*@
  loop invariant z + w == x + y + 1;;
  loop invariant z % 2 == x % 2;
  loop invariant y; <= z;
  loop invariant y == z;
  loop invariant y == z / 2;
  loop invariant y <= z;
  loop invariant y <= z + 1;;
  loop invariant y % 2 == z % 2;;
  loop invariant y % 2 == z % 2;
  loop invariant x; <= w;
  loop invariant x == y || x == y - 1;
  loop invariant x == w - 1;
  loop invariant x <= z;
  loop invariant x <= y;;
  loop invariant x <= w;
  loop invariant x + z <= w + y;
  loop invariant x + y == w + z;
  loop invariant x + y <= z + w;
  loop invariant x + y <= w + z;;
  loop invariant x + y <= w + z;
  loop invariant x % 2 == w % 2;;
  loop invariant x % 2 == w % 2;
  loop invariant w - z == 1;
  loop invariant w % 2 == z % 2;
  loop invariant \forall integer k; k >= 0 ==> (k == x || k == y || k <= w);
  loop invariant \forall integer k; 0 <= k < y ==> k % 2 == 0 || k % 2 == 1;
  loop invariant \forall integer i; 0 <= i ==> x + y <= w + z;
  loop invariant \exists integer k; k == w + z && k % 2 == 1;
  loop invariant 1; <= w;
  loop invariant 1 <= w + x + y + z;
  loop invariant 0; <= z;
  loop invariant 0; <= y;
  loop invariant 0; <= x;
  loop invariant (z + w) % 2 == 1;
  loop invariant (z % 2 == 0 && y % 2 == 0) || (z % 2 == 1 && y % 2 == 1);
  loop invariant (y == z) ==> x < w;
  loop invariant (x + y) <= w + z;
  loop invariant (x + y + z + w) % 2 == 0;;
  loop invariant (x + y + w + z) % 2 == 1;
  loop invariant (x % 2 == y % 2) || (x % 2 != y % 2);
  loop invariant (w + z) % 2 == (x + y) % 2;
  loop invariant z % 2 == 0 || z % 2 == 1;
  loop invariant y >= 0 && y <= z + 1;
  loop invariant x >= 0 && x <= w;
  loop invariant x <= y;
  loop invariant w % 2 == 0 || w % 2 == 1;
  loop invariant 1 <= w;
  loop invariant 0 <= z;
  loop invariant 0 <= y;
  loop invariant 0 <= x;
  loop invariant (w + z) % 2 == 1;
  loop invariant (w % 2 == 0 && z % 2 == 1) || (w % 2 == 1 && z % 2 == 0);
  loop assigns z;
  loop assigns y;
  loop assigns x;
  loop assigns w;
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

  // @ assert x <= 1;

}