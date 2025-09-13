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
  ```c
  loop invariant x == y;
  loop invariant x == a + c;
  loop invariant y == b + d;
  loop invariant x + y == 2 * (a + c);
  loop invariant a + c == b + d;
  loop invariant c <= 2;
  loop invariant b <= c;
  loop invariant b <= 2;
  loop assigns x, y, a, b, c, d;
  ```
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
    loop invariant y == b + d;
    loop invariant x == y;
    loop invariant x == a + c;
    loop invariant x + y == 2 * (a + c);
    loop invariant c <= 2;
    loop invariant b <= c;
    loop invariant b <= 2;
    loop invariant b <= 1;
    loop invariant a + c == b + d;
    loop invariant \forall integer i; 0 <= i <= c ==> c + b >= 0;
    loop invariant \forall integer i; 0 <= i <= b ==> c + b >= 0;
    loop invariant 0 <= c;
    loop invariant 0 <= b;
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