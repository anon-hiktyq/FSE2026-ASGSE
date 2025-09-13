/*@
requires i == 1;
requires j == 20;
*/
void foo(int i, int j) {
  // loop body
  /*@
  loop invariant 1 <= i <= j + 20;
  loop invariant 13 <= j <= 20;
  loop invariant j >= i - 2;
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
