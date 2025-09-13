/*@
requires i == 1;
requires j == 20;
*/
void foo(int i, int j) {
  // loop body
  /*@
  loop invariant i == 1 + 2 * (j_initial - j);
  loop invariant j_initial == 20;
  loop invariant 0 <= j <= j_initial;
  loop invariant j >= i;
  loop assigns i;
  loop assigns j;
  */
  while (j >= i) {
    i  = i + 2;
    j  = j - 1;
  }

}
