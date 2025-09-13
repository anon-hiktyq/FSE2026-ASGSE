int unknown1();
int unknown2();
int unknown3();

void foo036(int flag) {
  int a = 0;
  int b = 0;
  int x = 0;
  int y = 0;
  int z = 0;
  int j = 0;
  int w = 0;

 
  /*@
  loop invariant w >= z;
  loop invariant x + y + 1 == w;
  loop invariant x % 2 == 0 || x % 2 == 1;
  loop invariant z >= 0;
  loop invariant x >= 0;
  loop invariant y >= 0;
  loop invariant a - b == 0;
  loop assigns z, w, x, y, a, b;
  */
  while (unknown1()) {
    int i = z;
    int j = w;
    int k = 0;
    /*@
    loop invariant z <= i;
    loop invariant k == j - i;
    loop invariant k == i - z;
    loop invariant k <= w - z;
    loop invariant j == w;
    loop invariant i <= w;
    loop invariant i <= j;
    loop invariant 0 <= k;
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
    loop invariant z <= x;
    loop invariant z <= w;
    loop invariant z < w;
    loop invariant z + 1 <= x;
    loop invariant y == x - z - 1;
    loop invariant y <= w - z - 1;
    loop invariant y % 2 == 0 || y % 2 == -1;
    loop invariant x + y == w - 1;
    loop invariant x + y == 2*(z - 1) + w;
    loop invariant x % 2 == 1 || y % 2 == 1;
    loop invariant x % 2 == 0;
    loop invariant x % 2 == 0 || x % 2 == 1;
    loop invariant w == x + y + 1;
    loop invariant 0 <= y;
    loop invariant 0 <= x;
    loop assigns z;
    loop assigns y;
    loop assigns x;
    loop assigns w;
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
  // @ assert w >= z && a - b == 0;*/
}