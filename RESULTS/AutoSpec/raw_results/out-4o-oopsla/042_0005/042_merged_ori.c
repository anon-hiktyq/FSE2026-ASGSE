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
  loop invariant y - 1 <= x;
  loop invariant x - y == \at(x - y, Pre);
  loop invariant x - y == 0 || x - y == 1;
  loop invariant x - y == (flag ? 0 : -1);
  loop invariant x - y == (\at(x, Pre) - \at(y, Pre));
  loop invariant flag ==> a % 2 == (x + y) % 2;
  loop invariant a <= x + y;
  loop invariant a % 2 == 0 || a % 2 == 1;
  loop invariant \forall integer k; 0 <= k ==> (a >= 0);
  loop invariant \exists integer k; 0 <= k;
  loop invariant 3 <= x + y;
  loop invariant 2 <= x + y;
  loop invariant 2 <= (x + y);
  loop invariant (x + y) % 2 == (flag ? 0 : 1);
  loop invariant (flag ==> a % 2 == (x + y) % 2) && (!flag ==> a % 2 == (x + y + 1) % 2);
  loop invariant (a % 2 == 1) <==> ((x + y + flag) % 2 == 1);
  loop invariant (a % 2 == 1 && x >= y) || (a % 2 == 0 && y >= x);
  loop invariant (a % 2 == 0) || (a % 2 == 1);
  loop invariant (a % 2 == 0 && !flag) || (a % 2 == 1 && flag);
  loop invariant !flag ==> a % 2 == (x + y + 1) % 2;
  loop invariant x >= 1 && y >= 1;
  loop invariant a % 2 == 1 || a % 2 == 0;
  loop invariant a % 2 == (flag ? ((x + y) % 2) : ((x + y + 1) % 2));
  loop invariant 1 <= y;
  loop invariant 1 <= x;
  loop invariant 0 <= a;
  loop invariant (a % 2 == 1) || (a % 2 == 0);
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