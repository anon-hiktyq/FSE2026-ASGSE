int unknown1();
int unknown2();

void foo(int flag) {
  int x = 1;
  int y = 1;
  int a;

  if (flag)
    a = 0;
  else
    a = 1;

  /*@
  loop invariant x >= 1 && y >= 1;
  loop invariant x == y;
  loop invariant x == y || x == y + 1 || x + 1 == y;
  loop invariant flag ==> a % 2 == (x + y) % 2;
  loop invariant a == x + y || a == x + y + 1;
  loop invariant a % 2 == 1 || a % 2 == 0;
  loop invariant a % 2 == 1 ==> y >= x;
  loop invariant a % 2 == 0 ==> x >= y;
  loop invariant \forall integer k; x + y == 2*k + (a % 2);
  loop invariant 1 <= y;
  loop invariant 1 <= x;
  loop invariant (x + y) % 2 == 0;
  loop invariant (flag ==> x >= y) && (!flag ==> y >= x);
  loop invariant (flag ==> x + y >= 2) || (!flag ==> x + y >= 3);
  loop invariant (flag ==> a == x + y) || (!flag ==> a == x + y + 1);
  loop invariant (a % 2 == 1) ==> y >= x;
  loop invariant (a % 2 == 1 ==> y == x) || (a % 2 == 0 ==> y == x + 1);
  loop invariant (a % 2 == 1 ==> x == y) || (a % 2 == 0 ==> x == y + 1);
  loop invariant (a % 2 == 0) ==> x >= y;
  loop invariant !flag ==> a % 2 == (x + y + 1) % 2;
  loop assigns y;
  loop assigns x;
  loop assigns a;
  */
  while (unknown1()) {
    if (flag) {
      a = x + y;
      x++;
    } else {
      a = x + y + 1;
      y++;
    }
    if (a % 2 == 1)
      y++;
    else
      x++;
  }
  //x==y

  if (flag)
    a++;
  // @ assert a % 2 == 1;
}