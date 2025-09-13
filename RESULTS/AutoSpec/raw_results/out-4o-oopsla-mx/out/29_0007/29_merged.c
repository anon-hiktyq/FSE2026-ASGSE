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
    loop invariant x % 2 == y % 2;
    loop invariant c <= 2;
    loop invariant c + d == 4;
    loop invariant c + b == a + d;
    loop invariant b <= 1;
    loop invariant a - b == c - d;
    loop invariant a + c == b + d;
    loop invariant a + b == 2;
    loop invariant 0 <= d;
    loop invariant 0 <= c;
    loop invariant 0 <= b;
    loop invariant 0 <= a;
    loop assigns c;
    loop assigns b;
    */
    while (unknown2()) {
      c--;
      b--;
    }
  }
  // @ assert a + c == b + d;
}