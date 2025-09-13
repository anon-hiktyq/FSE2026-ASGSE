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
  loop invariant y <= x;
  loop invariant y <= x || x <= y + 1;
  loop invariant y <= x || x + y <= a;
  loop invariant y <= x || x + y - 1 <= a;
  loop invariant y <= x || a <= x + y + 1;
  loop invariant y <= x || \abs(x - y) <= 1;
  loop invariant y <= x || 2*y <= x + a;
  loop invariant y <= x || 1 <= a;
  loop invariant y <= x || 0 <= y;
  loop invariant y <= x || 0 <= x;
  loop invariant y < x;
  loop invariant x > 0 && y > 0;
  loop invariant x == y;
  loop invariant x == y || x == y + 1;
  loop invariant x == y || x + 1 == y;
  loop invariant x == y || x != y;
  loop invariant x <= y + 1;
  loop invariant x <= y + 1 || 2*y <= x + a;
  loop invariant x <= y + 1 || 1 <= a;
  loop invariant x <= y + 1 || 0 <= x;
  loop invariant x < y + 1;
  loop invariant x + y <= a;
  loop invariant x + y <= a || x <= y + 1;
  loop invariant x + y <= a || x + y - 1 <= a;
  loop invariant x + y <= a || a <= x + y + 1;
  loop invariant x + y <= a || 2*y <= x + a;
  loop invariant x + y <= a || 1 <= a;
  loop invariant x + y <= a || 0 <= x;
  loop invariant x + y < a;
  loop invariant x + y - 1 <= a;
  loop invariant x + y - 1 <= a || x <= y + 1;
  loop invariant x + y - 1 <= a || a <= x + y + 1;
  loop invariant x + y - 1 <= a || 2*y <= x + a;
  loop invariant x + y - 1 <= a || 1 <= a;
  loop invariant x + y - 1 <= a || 0 <= x;
  loop invariant x + y - 1 < a;
  loop invariant flag ==> a == x + y;
  loop invariant flag ==> (a % 2 == 1);
  loop invariant a == x + y + (x - y);
  loop invariant a <= x + y + 1;
  loop invariant a <= x + y + 1 || x <= y + 1;
  loop invariant a <= x + y + 1 || 2*y <= x + a;
  loop invariant a <= x + y + 1 || 1 <= a;
  loop invariant a <= x + y + 1 || 0 <= x;
  loop invariant a < x + y + 1;
  loop invariant a % 2 == 1 || a % 2 == 0;
  loop invariant \valid(&x) && \valid(&y) && \valid(&a);
  loop invariant \forall integer p, q; 0 <= p < x && 0 <= q < y ==> a >= p + q;
  loop invariant \forall integer n; 0 <= n <= x ==> x + y >= 2 * n;
  loop invariant \exists integer k; a == x + y + k;;
  loop invariant \abs(x - y) <= 1;
  loop invariant \abs(x - y) <= 1 || x <= y + 1;
  loop invariant \abs(x - y) <= 1 || x + y <= a;
  loop invariant \abs(x - y) <= 1 || x + y - 1 <= a;
  loop invariant \abs(x - y) <= 1 || a <= x + y + 1;
  loop invariant \abs(x - y) <= 1 || 2*y <= x + a;
  loop invariant \abs(x - y) <= 1 || 1 <= a;
  loop invariant \abs(x - y) <= 1 || 0 <= x;
  loop invariant \abs(x - y) < 1;
  loop invariant 2*y <= x + a;
  loop invariant 2*y <= x + a || 0 <= x;
  loop invariant 2*y < x + a;
  loop invariant 1 <= a;
  loop invariant 1 <= a || 2*y <= x + a;
  loop invariant 1 <= a || 0 <= x;
  loop invariant 1 < a;
  loop invariant 0 <= y;
  loop invariant 0 <= y || x <= y + 1;
  loop invariant 0 <= y || x + y <= a;
  loop invariant 0 <= y || x + y - 1 <= a;
  loop invariant 0 <= y || a <= x + y + 1;
  loop invariant 0 <= y || \abs(x - y) <= 1;
  loop invariant 0 <= y || 2*y <= x + a;
  loop invariant 0 <= y || 1 <= a;
  loop invariant 0 <= y || 0 <= x;
  loop invariant 0 <= x;
  loop invariant 0 < y;
  loop invariant 0 < x;
  loop invariant (flag ==> y >= x) || (!flag ==> x >= y);
  loop invariant (flag ==> x >= y) || (!flag ==> y >= x);
  loop invariant (flag ==> x == y) || (!flag ==> a == x + y + 1);;
  loop invariant (flag ==> x <= y) || (!flag ==> y <= x);
  loop invariant (flag ==> x <= y + 1) && (!flag ==> y <= x);
  loop invariant (flag ==> a > 0) || (!flag ==> a >= 1);
  loop invariant (flag ==> a % 2 == 0) || (!flag ==> a % 2 == 1);
  loop invariant (flag ==> a % 2 == (x + 1) % 2) || (!flag ==> a % 2 == x % 2);
  loop invariant (flag ==> (a % 2 == 0)) || (!flag ==> (a % 2 == 1));
  loop invariant (flag && a == x + y) || (!flag && a == x + y + 1);
  loop invariant (flag && a % 2 == 0) || (!flag && a % 2 == 1);
  loop invariant (a % 2 == 1 || a % 2 == 0);
  loop invariant !flag ==> a == x + y + 1;
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