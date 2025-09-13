int unknown1();
int unknown2();
int unknown3();

void foo(int flag) {
  int a = 0;
  int b = 0;
  int x = 0;
  int y = 0;
  int z = 0;
  int j = 0;
  int w = 0;

  while (unknown1()) {
    int i = z;
    int j = w;
    int k = 0;
    /*@
    loop invariant z <= i;
    loop invariant k == j - i;
    loop invariant k == i - z;
    loop invariant i <= w;
    loop invariant i <= j;
    loop assigns k;
    loop assigns i;
    */
    while (i < j) {
      k++;
      i++;
    }

    x = z;
    y = k;

    if (x % 2 == 1) {
      x++;
      y--;
    }

    /*@
    } else {;
    y--;
    y -= 2;
    x--;
    x += 2;
    loop invariant z <= x;
    loop invariant y == w - x - 1;
    loop invariant y <= w;
    loop invariant x + y == z + w - 1;
    loop invariant x + y == w - 1;
    loop invariant x + y == \at(x, LoopEntry) + \at(y, LoopEntry);
    loop invariant x + y == \at(x + y, Pre);
    loop invariant x + y == 2 * z + 1;
    loop invariant x % 2 == y % 2;
    loop invariant x % 2 == 0;
    loop invariant x % 2 == 0 || x % 2 == 1;
    loop invariant \exists integer n; x == z + 2*n || x == z + 2*n + 1;
    loop invariant \exists integer m; y == w - 2*m || y == w - 2*m - 1;
    loop invariant 0 <= z;
    loop invariant 0 <= y;
    loop invariant 0 <= x;
    loop invariant 0 <= w;
    loop assigns y;
    loop assigns x;
    if (x % 2 == 0) {;
    ```c;
    ```;
    /*@;
    */
    while (unknown2()) {
      if (x % 2 == 0) {
        x += 2;
        y -= 2;
      } else {
        x--;
        y--;
      }
    }
    z++;
    w = x + y + 1;
  }

  int c = 0;
  int d = 0;
  while (unknown3()) {
    c++;
    d++;
    if (flag) {
      a++;
      b++;
    } else {
      a += c;
      b += d;
    }
  }
  // @ assert w >= z && a - b == 0;
}