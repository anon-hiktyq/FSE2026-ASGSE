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
  loop invariant (x + y) % 2 == a % 2;
  loop invariant flag ==> ((x + y) % 2 == 0);
  loop invariant !flag ==> ((x + y) % 2 == 1);
  loop assigns x, y, a;
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