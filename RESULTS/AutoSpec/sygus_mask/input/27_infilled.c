/*@
requires x == n;
requires n >= 0;
*/
void foo(int x, int n) {
  // loop body
  /* @ >>> INFILL <<< */
  while (x > 1) {
    x  = x - 1;
  }

}