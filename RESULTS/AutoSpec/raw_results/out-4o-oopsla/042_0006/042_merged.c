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
  loop invariant x - y <= 1;
  loop invariant x - y <= 1 || 2 <= x + y;
  loop invariant x - y < 1;
  loop invariant x - 1 <= y;
  loop invariant x - 1 <= y || x - y <= 1;
  loop invariant x - 1 <= y || 2 <= x + y;
  loop invariant x - 1 < y;
  loop invariant x + y <= a || x - y <= 1;
  loop invariant x + y <= a || x - 1 <= y;
  loop invariant x + y <= a || 2 <= x + y;
  loop invariant a <= x + y + flag || x - y <= 1;
  loop invariant a <= x + y + flag || x - 1 <= y;
  loop invariant a <= x + y + flag || a <= x + y + 1;
  loop invariant a <= x + y + flag || 2 <= x + y;
  loop invariant a <= x + y + 1;
  loop invariant a <= x + y + 1 || x - y <= 1;
  loop invariant a <= x + y + 1 || x - 1 <= y;
  loop invariant a <= x + y + 1 || x + y <= a;
  loop invariant a <= x + y + 1 || 2 <= x + y;
  loop invariant a < x + y + 1;
  loop invariant a % 2 == (x + y) % 2 || a % 2 == (x + y + 1) % 2;
  loop invariant \forall integer k; 0 <= k ==> a >= 0;
  loop invariant 0 <= a || x - y <= 1;
  loop invariant 0 <= a || x - 1 <= y;
  loop invariant 0 <= a || x + y <= a;
  loop invariant 0 <= a || a <= x + y + flag;
  loop invariant 0 <= a || a <= x + y + 1;
  loop invariant 0 <= a || 2 <= x + y;
  loop invariant x >= 1 && y >= 1;
  loop invariant flag ==> a % 2 == (x + y) % 2;
  loop invariant a <= x + y;
  loop invariant a % 2 == 1 || a % 2 == 0;
  loop invariant a % 2 == 0 || a % 2 == 1;
  loop invariant a % 2 == (flag ? ((x + y) % 2) : ((x + y + 1) % 2));
  loop invariant \forall integer k; 0 <= k ==> (a >= 0);
  loop invariant \exists integer k; 0 <= k;
  loop invariant 2 <= x + y;
  loop invariant 2 <= (x + y);
  loop invariant 1 <= y;
  loop invariant 1 <= x;
  loop invariant 0 <= a;
  loop invariant (flag ==> a % 2 == (x + y) % 2) && (!flag ==> a % 2 == (x + y + 1) % 2);
  loop invariant (a % 2 == 1) || (a % 2 == 0);
  loop invariant (a % 2 == 0) || (a % 2 == 1);
  loop invariant !flag ==> a % 2 == (x + y + 1) % 2;
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