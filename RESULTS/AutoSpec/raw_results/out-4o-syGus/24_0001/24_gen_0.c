/*@
requires i == 1;
requires j == 20;
*/
void foo(int i, int j) {
  // loop body
  /*@
  loop invariant 1 <= i <= j+2;
  loop invariant j >= 6;
  loop invariant i % 2 == 1;
  loop invariant 21 <= i + j <= 22;
  loop assigns i;
  loop assigns j;
  */
  while (j >= i) {
    i  = i + 2;
    j  = j - 1;
  }
  // post-condition
  // @ assert j == 6;
}
