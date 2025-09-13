
int unknown1();
int unknown2();

void foo06() {
  int w = 1;
  int z = 0;
  int x = 0;
  int y = 0;

  
  while(unknown1()) {
	  
    /*@
    loop invariant x == y;
    loop invariant z == x + y;
    loop invariant w == z + 1;
    loop invariant w % 2 == 1;
    loop assigns x;
    loop assigns y;
    loop assigns z;
    loop assigns w;
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
