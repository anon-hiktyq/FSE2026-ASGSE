int unknown1();
int unknown2();

void foo029() {
  int a = 1;
  int b = 1;
  int c = 2;
  int d = 2;
  int x = 3;
  int y = 3;
 
  /*@
  loop invariant y == x;
  loop invariant x == y;
  loop invariant c <= 2;
  loop invariant b <= c;
  loop invariant b <= 2;
  loop invariant a + c == b + d;
  loop invariant \forall integer i; 0 <= i <= b ==> c + b >= 0;
  loop invariant (x + y) % 2 == 0;
  loop assigns y;
  loop assigns x;
  loop assigns d;
  loop assigns c;
  loop assigns b;
  loop assigns a;
  */
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
    loop invariant x == y;
    loop invariant c <= 2;
    loop invariant b <= c;
    loop invariant b <= 2;
    loop invariant a + c == b + d;
    loop invariant \forall integer i; 0 <= i <= b ==> c + b >= 0;
    loop assigns y;
    loop assigns x;
    loop assigns d;
    loop assigns c;
    loop assigns b;
    loop assigns a;
    */
    while (unknown2()) {
      c--;
      b--;
    }
  }
  //@assert a + c == b + d;
}