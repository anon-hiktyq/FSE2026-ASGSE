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
  loop invariant x >= 1;
  loop invariant y >= 1;
  loop invariant (flag ==> x >= y) && (!flag ==> y >= x);
  loop invariant (a % 2 == 1 ==> y == x) || (a % 2 == 0 ==> y == x + 1);
  loop invariant (a % 2 == 1 ==> x == y) || (a % 2 == 0 ==> x == y + 1);
  loop assigns a, x, y;
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