int unknown1();
int unknown2();
int unknown3();

void main() {
  int a = 1;
  int b = 1;
  int c = 2;
  int d = 2;
  int x = 3;
  int y = 3;
  /*@
  loop invariant y == b + d;
  loop invariant x == a + c;
  loop invariant a + c == b + d;
  loop invariant x == y;
  loop invariant c <= 2;
  loop invariant b <= 2;
  loop invariant 0 <= a;
  loop invariant 0 <= b;
  loop invariant 0 <= c;
  loop invariant 0 <= d;
  loop invariant a <= x;
  loop invariant b <= y;
  loop invariant x + y == 2*a + 2*c;
  loop assigns a, b, c, d, x, y;
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
    loop invariant x + y == 2*a + 2*c;
    loop invariant c <= 2;
    loop invariant b <= y;
    loop invariant b <= 2;
    loop invariant a <= x;
    loop invariant a + c == b + d;
    loop invariant \exists integer k; 0 <= k ==> (x + y + 2*k) % 2 == 0;
    loop invariant 0 <= c;
    loop invariant 0 <= b;
    loop invariant 0 <= a;
    loop invariant 0 <= a && 0 <= b && 0 <= c && 0 <= d;
    loop assigns \nothing;
    */
    while (unknown2()) {
      c--;
      b--;
    }
  }
  // @ assert a + c == b + d;
}