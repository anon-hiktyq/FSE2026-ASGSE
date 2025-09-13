
int unknown();


void foo046() {

  int w = 1;
  int z = 0;
  int x = 0;
  int y = 0;


  /*@
  loop invariant w >= 1;
  loop invariant z >= 0;
  loop invariant x <= w;
  loop invariant y <= z + 1;
  loop invariant x <= 1;
  loop assigns w;
  loop assigns z;
  loop assigns x;
  loop assigns y;
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