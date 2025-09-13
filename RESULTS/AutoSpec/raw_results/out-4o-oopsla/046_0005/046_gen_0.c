
int unknown();


void foo046() {

  int w = 1;
  int z = 0;
  int x = 0;
  int y = 0;


  /*@
  loop invariant x + y <= w + z;
  loop invariant x % 2 == w % 2;
  loop invariant y % 2 == z % 2;
  loop invariant x + z <= w + y;
  loop invariant (x % 2 == y % 2) || (x % 2 != y % 2);
  loop invariant w >= x;
  loop invariant z >= y;
  loop invariant x <= z;
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