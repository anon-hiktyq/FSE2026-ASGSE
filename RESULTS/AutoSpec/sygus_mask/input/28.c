/*@
requires x == n;
requires x != 0;
*/
void foo(int x, int n) { 
  // loop body
  while (x > 0) {
    x  = x - 1;
  }

}
