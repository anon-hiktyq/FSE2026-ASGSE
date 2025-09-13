/*@
requires i == 1;
requires j == 20;
*/
void foo(int i, int j) {
  // loop body
  /*@
  loop invariant i == 1 + 2 * (20 - j);
  loop invariant 13 <= j <= 20;
  loop invariant j % 2 == 0;
  loop invariant j >= i - 1;
  loop assigns i, j;
  */
  while (j >= i) {
    i  = i + 2;
    j  = j - 1;
  }
  // post-condition
  // @ assert j == 13;
}
