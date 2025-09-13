/*@
requires i == 1;
requires j == 20;
*/
void foo(int i, int j) {
  // loop body
  /*@
  loop invariant i == 1 + 2 * (j0 - j);
  loop invariant 1 <= i;
  loop invariant j0 == j + (j0 - j);
  loop invariant j >= i;
  loop assigns i;
  loop assigns j;
  */
  while (j >= i) {
    i  = i + 2;
    j  = j - 1;
  }

}
