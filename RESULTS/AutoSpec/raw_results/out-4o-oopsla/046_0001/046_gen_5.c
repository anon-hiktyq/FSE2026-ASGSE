
int unknown();


void foo046() {

  int w = 1;
  int z = 0;
  int x = 0;
  int y = 0;


  /*@
  loop invariant x <= w;
  loop invariant y <= z;
  loop invariant w >= 1;
  loop invariant z >= 0;
  loop invariant w % 2 == 0 ==> x == y;
  loop invariant z % 2 == 1 ==> x == y;
  loop assigns w, z, x, y;
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