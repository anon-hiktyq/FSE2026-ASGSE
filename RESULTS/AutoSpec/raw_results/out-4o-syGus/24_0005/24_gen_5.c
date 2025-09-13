/*@
requires i == 1;
requires j == 20;
*/
void foo(int i, int j) {
  // loop body
  /*@
  loop invariant i <= j + 2;
  loop invariant j >= 6;
  loop invariant (j - i) % 3 == 17;
  loop invariant i >= 1;
  loop invariant j <= 20;
  loop assigns i, j;
  */
  while (j >= i) {
    i  = i + 2;
    j  = j - 1;
  }
  // post-condition
  // @ assert j == 6;
}
