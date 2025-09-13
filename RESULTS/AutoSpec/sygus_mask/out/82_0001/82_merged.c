/*@
requires x >= 0;
requires y >= 0;
requires x >= y;
*/
void foo(int x, int y) {
  int i = 0;
  
  /*@
  loop invariant y <= x;
  loop invariant i <= y;
  loop invariant i < y ==> \forall integer k; 0 <= k < i ==> k < y;
  loop invariant \forall integer k; 0 <= k < i ==> k < y;
  loop invariant 0 <= i;
  loop assigns y;
  loop assigns x;
  loop assigns i;
  */
  while (unknown()) {
    if (i < y)
    {
      i = i + 1;
    }
  }

}
