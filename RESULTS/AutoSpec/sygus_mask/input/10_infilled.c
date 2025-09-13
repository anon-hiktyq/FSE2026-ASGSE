/*@
  requires 0 <= x <= 2;
  requires 0 <= y <= 2;
*/
void foo(int x, int y) {
  // loop body
  /* @ >>> INFILL <<< */
  while (unknown()) {
    x  = x + 2;
    y  = y + 2;
  }

}
