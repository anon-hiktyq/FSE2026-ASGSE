/*@
requires i == 1;
requires j == 20;
*/
void foo(int i, int j) {
  // loop body
  /*@
  loop invariant i <= j + 1;
  loop invariant i >= 1;
  loop invariant j <= 20;
  loop invariant i % 2 == 1;
  loop invariant j == 20 - (i - 1) + (i - 1) / 2;
  loop assigns i;
  loop assigns j;
  */
  while (j >= i) {
    i  = i + 2;
    j  = j - 1;
  }
  // post-condition
  // @ assert j == 13;
}
