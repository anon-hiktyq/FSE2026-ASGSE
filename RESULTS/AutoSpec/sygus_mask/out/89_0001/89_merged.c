/*@
requires x == y;
*/
void foo(int x, int y) {
  int lock = 1;
  
  /*@
  loop invariant x == y;
  loop invariant x == y || x != y;
  loop invariant x == y ==> lock == 1;
  loop invariant x != y ==> (lock == 1 || lock == 0);
  loop invariant lock == 1 || lock == 0;
  loop invariant lock == (x == y ? 1 : 0);
  loop invariant \forall integer k; (lock == 1 ==> x == y);
  loop invariant \forall integer k; (lock == 0 ==> x == y + 1);
  loop invariant \forall int k; x == y ==> x == y;
  loop invariant \forall int k; k == x || k == y ==> x <= k;
  loop invariant \exists int k; k >= 0 && x == y + k;
  loop invariant \exists int k; k >= 0 && k < 2 ==> (lock == k ==> x == y + k);
  loop assigns y;
  loop assigns x;
  loop assigns lock;
  */
  while (x != y) {  
    if (unknown()) {
      lock = 1;
      x = y;
    } else {
      lock  = 0;
      x  = y;
      y  = y + 1; 
    }
  }

}
