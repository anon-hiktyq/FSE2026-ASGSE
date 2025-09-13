/*@
requires i == 1;
requires j == 20;
*/
void foo(int i, int j) {
  // loop body
  /*@
  loop invariant i == 1 + 2 * (n - j);
  loop invariant j >= i;
  loop invariant j <= 20;
  loop invariant j >= 1;
  loop assigns i;
  loop assigns j;
  */
  while (j >= i) {
    i  = i + 2;
    j  = j - 1;
  }

}
