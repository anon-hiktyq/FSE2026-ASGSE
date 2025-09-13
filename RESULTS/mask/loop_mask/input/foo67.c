int unknown();
/*@
requires n > 0;
*/
void foo67(int n) {
  int x = 0;
  int m = 0;
 
  while (x < n) {
    if (unknown()) {
      m = x;
    }
    x = x + 1;
  }
  /* mask_1 */
}