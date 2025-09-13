
int unknown();


void foo046() {

  int w = 1;
  int z = 0;
  int x = 0;
  int y = 0;


  /*@
  loop invariant z % 2 == 1 ==> x == y;
  loop invariant z % 2 == 0 || z % 2 == 1;
  loop invariant z % 2 == (y % 2);
  loop invariant y <= z;
  loop invariant y <= z + 1;
  loop invariant x <= w;
  loop invariant x <= w - 1;
  loop invariant x <= 1;
  loop invariant w % 2 == 1 || w % 2 == 0;
  loop invariant w % 2 == 0 ==> x == y;
  loop invariant w % 2 == (x % 2);
  loop invariant 1 <= w;
  loop invariant 0 <= z;
  loop invariant 0 <= y;
  loop invariant 0 <= x;
  loop invariant (z % 2 == 0) ==> (y == \old(y) + 1 && z == \old(z) + 1);
  loop invariant (w % 2 == 1) ==> (x == \old(x) + 1 && w == \old(w) + 1);
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