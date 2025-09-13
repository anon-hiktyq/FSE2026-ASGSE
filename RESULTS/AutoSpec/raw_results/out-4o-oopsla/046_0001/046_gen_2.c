
int unknown();


void foo046() {

  int w = 1;
  int z = 0;
  int x = 0;
  int y = 0;


  /*@
  loop invariant w >= 1;
  loop invariant z >= 0;
  loop invariant x >= 0;
  loop invariant y >= 0;
  loop invariant (w % 2 == 1) ==> (x == \old(x) + 1 && w == \old(w) + 1);
  loop invariant (z % 2 == 0) ==> (y == \old(y) + 1 && z == \old(z) + 1);
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