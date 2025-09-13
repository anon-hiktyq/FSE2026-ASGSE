/*@
requires n < 0;
*/
void foo(int n) {
  int x = n;
  // loop body
  /* @ >>> INFILL <<< */
  while (x > 0) {
    x  = x - 1;
  }

}
