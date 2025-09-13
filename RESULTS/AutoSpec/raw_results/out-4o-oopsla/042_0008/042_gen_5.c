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
  loop invariant 1 <= x;
  loop invariant 1 <= y;
  loop invariant 2 <= x + y;
  loop invariant (x % 2 == 1) && (y % 2 == 1);
  loop invariant (flag ==> a == x + y - 1) || (!flag ==> a == x + y);
  loop invariant \forall integer k; x + y >= 2 * k + 2 ==> (x % k == y % k);
  loop invariant a % 2 == 1 || a % 2 == 0;
  loop invariant a % 2 == (flag ? 0 : 1);
  loop invariant 2 <= x + y;
  loop invariant 1 <= y;
  loop invariant 1 <= x;
  loop invariant (x + y) % 2 == 0;
  loop invariant (flag ==> a == x + y - 1) || (!flag ==> a == x + y);
  loop invariant (flag ==> a % 2 == 1) || (!flag ==> a % 2 == 0);
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