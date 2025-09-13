
int unknown1();
int unknown2();

void foo06() {
  int w = 1;
  int z = 0;
  int x = 0;
  int y = 0;

  
  /*@
  loop invariant z == x + y;
  loop invariant z == 2 * x;
  loop invariant z % 2 == 0;
  loop invariant x == y;
  loop invariant w == z + 1;
  loop invariant w == 2 * x + 1;
  loop invariant w % 2 == 1;
  loop invariant 1 <= w;
  loop invariant 0 <= z;
  loop invariant 0 <= y;
  loop invariant 0 <= x;
  loop assigns z;
  loop assigns w;
  loop assigns x;
  loop assigns y;
  */
  while(unknown1()) {
	  
    /*@
    loop invariant z == x + y;
    loop invariant z == 2*x;
    loop invariant z == 2 * x;
    loop invariant z % 2 == 0;
    loop invariant x == y;
    loop invariant x <= y;
    loop invariant w == z + 1;
    loop invariant w == 2*x + 1;
    loop invariant w % 2 == z % 2;
    loop invariant w % 2 == 1;
    loop invariant 1 <= w;
    loop invariant 0 <= z;
    loop invariant 0 <= y;
    loop invariant 0 <= x;
    loop assigns y;
    loop assigns x;
    */
    while(unknown2()){
      if(w%2 == 1) x++;
      if(z%2 == 0) y++;
    }
    z = x + y;
    w = z + 1;
  }

   // @ assert x == y;
}
