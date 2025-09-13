
void foo70(int flag) {
  int x = 1;
  int y = 1;
  int a;

  if (flag)
    a = 0;
  else
    a = 1;

  /* >>> LOOP INVARIANT TO FILL <<< */
  /*@
    loop invariant x >= 1 && y >= 1;
    loop invariant \at(flag,Pre) == flag;
    loop invariant flag != 0 ==> a == x + y;
    loop invariant flag == 0 ==> a == x + y + 1;
    loop invariant a >= x + y;
    loop invariant a % 2 == 1 ==> y >= \at(y,Pre) + (\at(x,Pre) - x);
    loop invariant a % 2 == 0 ==> x >= \at(x,Pre) + (\at(y,Pre) - y);
    loop variant x + y;
  */
  while (unknown()) {
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

  if (flag) {
    a++;
  }
  /*@ assert a % 2 == 1; */
}
