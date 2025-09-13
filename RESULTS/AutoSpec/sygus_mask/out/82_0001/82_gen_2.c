/*@
requires x >= 0;
requires y >= 0;
requires x >= y;
*/
void foo(int x, int y) {
  int i = 0;
  
  /*@
  loop invariant 0 <= i <= y;
  loop invariant \forall integer k; 0 <= k < i ==> k < y;
  loop assigns i;
  loop assigns x;
  loop assigns y;
  */
  while (unknown()) {
    if (i < y)
    {
      i = i + 1;
    }
  }

}
