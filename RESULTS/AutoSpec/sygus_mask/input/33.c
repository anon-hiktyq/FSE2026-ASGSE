/*@
requires n < 0;
*/
void foo(int n) {
  int x = n;
  // loop body
  while (x > 0) {
    x  = x - 1;
  }

}
