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
  loop invariant a >= x + y;
  loop invariant a % 2 == 1 || a % 2 == 0;
  loop invariant x >= 1 && y >= 1;
  loop invariant x >= y || y >= x;
  loop invariant (flag ==> x >= y) || (!flag ==> y >= x);
  loop invariant \forall integer p, q; 0 <= p < x && 0 <= q < y ==> a >= p + q;
  loop invariant 2 <= x + y;
  loop invariant x >= y || y >= x;
  loop invariant x >= 1 && y >= 1;
  loop invariant a % 2 == 0 || a % 2 == 1;
  loop invariant 2 <= x + y;
  loop invariant 1 <= y;
  loop invariant 1 <= x;
  loop invariant 0 <= a;
  loop invariant (flag ==> x >= y) && (!flag ==> y >= x);
  loop invariant (flag ==> a == x + y) || (!flag ==> a == x + y + 1);
  loop invariant (flag ==> a % 2 == 1) || (!flag ==> a % 2 == 0);
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