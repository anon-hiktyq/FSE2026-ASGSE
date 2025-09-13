
int unknown();


void foo046() {

  int w = 1;
  int z = 0;
  int x = 0;
  int y = 0;


  /*@
  loop invariant x <= 1;
  loop invariant w >= 1;
  loop invariant z >= 0;
  loop invariant y <= z;
  loop invariant w % 2 == (x % 2 ? 0 : 1);
  loop invariant z % 2 == (y % 2 ? 1 : 0);
  loop assigns x, y, w, z;
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