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
  loop invariant y == b + d;
  loop invariant y == 3;
  loop invariant y <= 3;
  loop invariant x == y;
  loop invariant x == a + c;
  loop invariant x == 3;
  loop invariant x <= 3;
  loop invariant x + y == 2 * (a + c);
  loop invariant d <= 2;
  loop invariant c <= 2;
  loop invariant b <= y;
  loop invariant b <= c;
  loop invariant b <= a;
  loop invariant b <= 2;
  loop invariant a <= x;
  loop invariant a + c == b + d;
  loop invariant \forall integer i; 0 <= i <= c ==> c + b >= 0;
  loop invariant \forall integer i; 0 <= i <= b ==> c + b >= 0;
  loop invariant 3 <= y;
  loop invariant 3 <= x;
  loop invariant 2 <= d;
  loop invariant 2 <= c;
  loop invariant 1 <= b;
  loop invariant 1 <= a;
  loop invariant 0 <= c;
  loop invariant 0 <= b;
  loop invariant 0 <= a;
  loop invariant (x + y) % 2 == 0;
  loop assigns y;
  loop assigns x;
  loop assigns d;
  loop assigns c;
  loop assigns b;
  loop assigns a;
  ```c;
  ```;
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