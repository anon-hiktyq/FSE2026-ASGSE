/*@
requires i == 1;
requires j == 20;
*/
void foo(int i, int j) {
  // loop body
  /*@
  loop invariant 1 <= i <= j + 2;
  loop invariant j >= 13;
  loop invariant (j - i) % 2 == 17;
  loop invariant j >= 0;
  loop assigns i, j;
  */
  while (j >= i) {
    i  = i + 2;
    j  = j - 1;
  }
  // post-condition
  // @ assert j == 13;
}
