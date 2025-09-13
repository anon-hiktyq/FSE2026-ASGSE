int unknown1();
int unknown2();

void foo029() {
  int a = 1;
  int b = 1;
  int c = 2;
  int d = 2;
  int x = 3;
  int y = 3;
 
  while (unknown1()) {
    x = a + c;
    y = b + d;

    if ((x + y) % 2 == 0) {
      a++;
      d++;
    } else {
      a--;
    }

   
    /*@
    loop invariant a + c == b + d;
    loop invariant x == y;
    loop invariant 0 <= c <= 2;
    loop invariant 0 <= b <= 1;
    loop assigns c;
    loop assigns b;
    */
    while (unknown2()) {
      c--;
      b--;
    }
  }
  //@assert a + c == b + d;
}