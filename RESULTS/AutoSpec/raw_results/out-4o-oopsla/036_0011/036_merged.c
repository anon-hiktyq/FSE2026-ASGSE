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
  loop invariant z <= w;
  loop invariant x >= 0 && y >= 0 && z >= 0;
  loop invariant x % 2 == 0;
  loop invariant x % 2 == 0 || x % 2 == 1;
  loop invariant flag ==> a == b;
  loop invariant a - b == 0;
  loop invariant \forall integer m; 0 <= m < z ==> w > m;
  loop invariant \at(x, LoopEntry) <= x;
  loop invariant 0 <= z;
  loop invariant 0 <= y;
  loop invariant 0 <= x;
  loop invariant 0 <= x + y;
  loop invariant 0 <= w;
  loop invariant (x % 2 == 0 && y % 2 == 0) || (x % 2 == 1 && y % 2 == 1);
  loop assigns z;
  loop assigns y;
  loop assigns x;
  loop assigns w;
  loop assigns flag;
  loop assigns b;
  loop assigns a;
  */
  while (unknown1()) {
    int i = z;
    int j = w;
    int k = 0;
    /*@
    loop invariant z <= i;
    loop invariant k == i - z;
    loop invariant k <= j - z;
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
    loop invariant x + y == \at(x + y, LoopEntry);
    loop invariant x % 2 == 0;
    loop invariant x % 2 == 0 || x % 2 == 1;
    loop invariant \at(x, LoopEntry) <= x;
    loop invariant 0 <= z;
    loop invariant 0 <= x;
    loop invariant 0 <= x + y;
    loop invariant (x % 2 == 0 && y % 2 == 0) || (x % 2 == 1 && y % 2 == 1);
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