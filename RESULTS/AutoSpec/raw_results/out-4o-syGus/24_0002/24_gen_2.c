/*@
requires i == 1;
requires j == 20;
*/
void foo(int i, int j) {
  // loop body
  /*@
  loop invariant j >= i - 1;
  loop invariant i % 2 == 1;
  loop invariant i >= 1;
  loop invariant j <= 20;
  loop invariant j >= 6;
  loop assigns i, j;
  */
  while (j >= i) {
    i  = i + 2;
    j  = j - 1;
  }
  // post-condition
  // @ assert j == 6;
}
