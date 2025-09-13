/*@
requires x == n;
requires x != 1;
*/
void foo(int x, int n) {
  // loop body
  /* @ >>> INFILL <<< */
  while (x > 1) {
    x  = x - 1;
  }

}
