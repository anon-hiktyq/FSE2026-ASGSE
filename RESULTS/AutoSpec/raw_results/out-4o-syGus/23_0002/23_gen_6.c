/*@
requires i == 1;
requires j == 20;
*/
void foo(int i, int j) {
  // loop body
  /*@
  loop invariant i <= j + 2;
  loop invariant i % 2 == 1;
  loop invariant j % 2 == 0;
  loop invariant 1 <= i <= j + 10;
  loop invariant 13 <= j <= 20;
  loop assigns i, j;
  */
  while (j >= i) {
    i  = i + 2;
    j  = j - 1;
  }
  // post-condition
  // @ assert j == 13;
}
