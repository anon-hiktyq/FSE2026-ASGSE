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
  loop invariant z <= x;
  loop invariant z <= w;
  loop invariant y == 0;
  loop invariant x == z + 2 * (w - z);
  loop invariant x % 2 == 0;
  loop invariant a == b;
  loop invariant a - b == 0;
  loop invariant \forall integer m; 0 <= m < z ==> x + y == m + 1;
  loop invariant \forall integer m; 0 <= m < x ==> (m % 2 == 0);
  loop invariant 0 <= z;
  loop invariant 0 <= y;
  loop invariant 0 <= x;
  loop invariant 0 <= b;
  loop invariant 0 <= a;
  loop assigns z;
  loop assigns y;
  loop assigns x;
  loop assigns w;
  loop assigns b;
  loop assigns a;
  */
  while (unknown1()) {
    int i = z;
    int j = w;
    int k = 0;
    /*@
    loop invariant z <= i;
    loop invariant x % 2 == 1 || x % 2 == 0;
    loop invariant k == i - z;
    loop invariant k <= w - z;
    loop invariant k <= j - z;
    loop invariant k <= j - i;
    loop invariant i == z + k;
    loop invariant i <= w;
    loop invariant i <= j;
    loop invariant i - z == k;
    loop invariant 0 <= k;
    loop invariant 0 <= i;
    loop assigns y;
    loop assigns x;
    loop assigns k;
    loop assigns j;
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
    loop invariant y == k - (x - z);
    loop invariant y == (x <= z ? 0 : k - (x - z));
    loop invariant y <= z - x;
    loop invariant y <= x;
    loop invariant y <= 0;
    loop invariant x == z + 2*(z - i);
    loop invariant x == z + 2 * (w - z);
    loop invariant x <= z + 2 * (w - z);
    loop invariant x + y == z * 2;
    loop invariant x + y == 2*(w - z) + 1;
    loop invariant x + 2*y == w - 1;
    loop invariant x % 2 == 1 || x % 2 == 0;
    loop invariant x % 2 == 1 ==> (y >= -2 * (w - x) - 1);
    loop invariant x % 2 == 0;
    loop invariant x % 2 == 0 || x % 2 == 1;
    loop invariant x % 2 == 0 ==> (y >= -2 * (w - x) - 2);
    loop invariant w == x + y + 1;
    loop invariant \forall integer n; z <= n < w ==> (x == n + 1 && y == 0) || (x == z && y == n - z + 1);
    loop invariant \forall integer m; z <= m < w ==> x + y == m + 1;
    loop invariant 0 <= y;
    loop invariant 0 <= x;
    loop invariant -(x - z) <= y;
    loop invariant (x + y <= w);
    loop invariant (x % 2 == 0 && y == (z - i)) || (x % 2 == 1 && y == (z - i - 1));
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