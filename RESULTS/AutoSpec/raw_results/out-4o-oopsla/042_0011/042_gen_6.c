int unknown();

void foo042(int flag) {
  int x = 1;
  int y = 1;
  int a;

  if (flag)
    a = 0;
  else
    a = 1;

  
  /*@
  loop invariant x >= 1 && y >= 1;
  loop invariant a % 2 == 0 || a % 2 == 1;
  loop invariant 1 <= y;
  loop invariant 1 <= x;
  loop invariant 0 <= a;
  loop invariant (flag ==> x >= y) && (!flag ==> y >= x);
  loop invariant (flag && x >= y) || (!flag && y >= x);
  loop invariant x <= y + 2;
  loop invariant y <= x + 2;
  loop invariant x >= 1 && y >= 1;
  loop invariant a % 2 == 0 || a % 2 == 1;
  loop invariant 1 <= y;
  loop invariant 1 <= x;
  loop invariant 0 <= a;
  loop invariant (flag ==> x >= y) && (!flag ==> y >= x);
  loop invariant (flag && x >= y) || (!flag && y >= x);
  loop assigns y;
  loop assigns x;
  loop assigns a;
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
  
  if (flag){
    a++;
  }
  // @ assert a % 2 == 1;
}