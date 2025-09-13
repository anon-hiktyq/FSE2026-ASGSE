
int unknown();


void foo046() {

  int w = 1;
  int z = 0;
  int x = 0;
  int y = 0;


  /*@
  loop invariant z >= y && z % 2 == y % 2;
  loop invariant z == y;
  loop invariant z % 2 == y % 2;
  loop invariant z % 2 == x % 2;
  loop invariant y + x <= w;
  loop invariant y % 2 == z % 2;
  loop invariant x >= 0 && y >= 0 && z >= 0;
  loop invariant x == w - 1;
  loop invariant x <= z;
  loop invariant x <= y;
  loop invariant x <= y + 1;
  loop invariant x <= w / 2;
  loop invariant x + y <= z + w;
  loop invariant x + y <= (w + z) / 2;
  loop invariant x + 1 <= w;
  loop invariant w % 2 == 0 || w % 2 == 1;
  loop invariant w % 2 == (x % 2) + 1 || w % 2 == x % 2;
  loop invariant \forall integer k; 0 <= k ==> (z % 2 == y % 2);
  loop invariant \forall integer k; 0 <= k ==> (w + z >= x + y);
  loop invariant \forall integer k; 0 <= k <= x ==> w >= k + 1;
  loop invariant \forall integer a; 0 <= a <= (z + w) ==> (a % 2 == 0 || a % 2 == 1);
  loop invariant 1 <= w - x;
  loop invariant 0 <= x && 0 <= y && 0 <= z && 1 <= w;
  loop invariant 0 < w;
  loop invariant z % 2 == 0 || z % 2 == 1;
  loop invariant z % 2 == (y % 2);
  loop invariant y <= z;
  loop invariant y <= z + 1;
  loop invariant x <= w;
  loop invariant x <= w - 1;
  loop invariant w % 2 == 1 || w % 2 == 0;
  loop invariant 1 <= w;
  loop invariant 0 <= z;
  loop invariant 0 <= y;
  loop invariant 0 <= x;
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