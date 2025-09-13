/*@
  requires 0 <= x <= 10;
  requires 0 <= y <= 10;
*/
void foo(int x, int y) {
  // loop body
  /*@
  loop invariant y <= \at(y, Pre) + 10 * (\at(x, Pre) / 10);
  loop invariant y <= 10 * (\at(y, Pre) / 10 + 1);
  loop invariant y - \at(y, Pre) <= 100;
  loop invariant x <= \at(x, Pre) + 10 * (\at(y, Pre) / 10);
  loop invariant x <= 20 || x >= 20;
  loop invariant x <= 10 * (\at(x, Pre) / 10 + 1);
  loop invariant x / 10 == (y / 10) + (\at(x, Pre) - \at(y, Pre)) / 10;
  loop invariant x - y == \at(x, Pre) - \at(y, Pre);
  loop invariant x - \at(x, Pre) <= 100;
  loop invariant x % 10 == y % 10;
  loop invariant x % 10 == \at(x, Pre) % 10 && y % 10 == \at(y, Pre) % 10;
  loop invariant \forall integer k; k >= 0 ==> (x == \at(x, Pre) + 10 * k && y == \at(y, Pre) + 10 * k);
  loop invariant \exists integer k; x == \at(x, Pre) + 10 * k && y == \at(y, Pre) + 10 * k;
  loop invariant \at(y, Pre) <= y;
  loop invariant \at(x, Pre) <= x;
  loop invariant (x == 20) ==> (y >= 10);
  loop invariant (x <= 10 && y <= 10) || (x > 10 && y > 10);
  loop invariant (x - y) == (\at(x, Pre) - \at(y, Pre));
  loop invariant y % 10 == \at(y, Pre) % 10;
  loop invariant x % 10 == \at(x, Pre) % 10;
  loop invariant 0 <= y;
  loop invariant 0 <= x;
  loop invariant (y - \at(y, Pre)) % 10 == 0;
  loop invariant (x - \at(x, Pre)) % 10 == 0;
  loop assigns y;
  loop assigns x;
  */
  while (unknown()) {
    x  = x + 10;
    y  = y + 10;
  }
  // post-condition
  if (x == 20) {
    // @ assert y != 0;
  }
}
