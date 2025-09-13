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
    ```c
    loop invariant x % 2 == y % 2;
    loop invariant x + y == 2 * (\at(x, Pre) / 2);
    loop invariant w == x + y + 1;
    loop invariant z <= w;
    loop invariant z <= x;
    loop invariant y >= 0;
    loop invariant 0 <= z;
    loop assigns x, y;
    ```
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