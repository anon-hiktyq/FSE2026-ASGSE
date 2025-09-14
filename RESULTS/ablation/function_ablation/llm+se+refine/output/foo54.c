
void foo54(int x, int y) {
  x = -50;

  /*@
    loop invariant x == -50 + \sum(0, y - \at(y, Pre) - 1, (\at(y, Pre) + i));
    loop invariant y > \at(y, Pre);
    loop invariant x < 0 ==> y > 0;
    loop invariant x < 0;
    loop assigns x, y;
    loop variant -x;
  */
  while (x < 0) {
    x = x + y;
    y++;
  }

  /*@ assert y > 0;*/
}
