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
  loop invariant a - b == 0;
  loop invariant x <= y;
  loop invariant x <= z;
  loop invariant x + y == w + z;
  loop invariant x + y == w;
  loop invariant x + y == w - z;
  loop invariant w == x + y + z;
  loop invariant w == x + y + z + 1;
  loop invariant w >= x + y;
  loop invariant w >= x + y + z;
  loop invariant w >= x + y;
  loop invariant w >= x + y + z;
  loop invariant w >= x + y + z + 1;
  loop invariant w >= z;
  loop invariant \forall integer n; z <= n < x ==> n < w;
  loop invariant \forall integer n; z <= n < x ==> n % 2 == 0;
  loop invariant \forall integer n; z <= n < w ==> n % 2 == 0;
  loop invariant \forall integer m; z <= m < w ==> m < w;
  loop invariant 0 <= z;
  loop invariant 0 <= x;
  loop invariant 0 <= y;
  loop assigns z, w, k, x, y;
  loop assigns c, d, a, b;
  */
  while (unknown1()) {
    int i = z;
    int j = w;
    int k = 0;
    /*@
    loop invariant z <= j;
    loop invariant z <= i;
    loop invariant k == i - z;
    loop invariant k <= j - z;
    loop invariant k <= j - i;
    loop invariant j <= w;
    loop invariant i == z + k;
    loop invariant i <= w;
    loop invariant i <= j;
    loop invariant i - z == k;
    loop invariant \forall integer m; z <= m < i ==> m < w;
    loop invariant 0 <= k;
    loop invariant 0 <= k == i - z;
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
    loop invariant y <= 0;
    loop invariant x + y == z + w - 1;
    loop invariant x + y == w - z - 1;
    loop invariant x + y == w - 1;
    loop invariant x + y <= 2 * w;
    loop invariant x % 2 == y % 2;
    loop invariant x % 2 == 1 ==> y == -1;
    loop invariant x % 2 == 0;
    loop invariant x % 2 == 0 ==> y % 2 == 0;
    loop invariant w == x + y + 1;
    loop invariant \forall integer n; z <= n < x ==> n % 2 == 0;
    loop invariant \forall integer n; z <= n < w ==> n % 2 == 0;
    loop invariant \forall integer m; z <= m < w ==> m < w;
    loop invariant \exists integer n; 0 <= n <= z && y == -2*n - 1;
    loop invariant \exists integer n; 0 <= n <= z && x == z + 2*n;
    loop invariant 0 <= z;
    loop invariant 0 <= y;
    loop invariant 0 <= x;
    loop assigns y;
    loop assigns x;
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