/*@
requires i == 1;
requires j == 20;
*/
void foo(int i, int j) {
  // loop body
  /*@
  loop invariant i == 1 + 2 * (k - 1);
  loop invariant j == 20 - (k - 1);
  loop invariant k >= 1;
  loop invariant j >= i;
  loop assigns i;
  loop assigns j;
  */
  while (j >= i) {
    i  = i + 2;
    j  = j - 1;
  }

}
