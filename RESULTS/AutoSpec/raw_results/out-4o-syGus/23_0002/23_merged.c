/*@
requires i == 1;
requires j == 20;
*/
void foo(int i, int j) {
  // loop body
  /*@
  loop invariant j == 20 - (i - 1) + (i - 1) / 2;
  loop invariant j <= 20;
  loop invariant i <= j + 3;
  loop invariant i <= j + 2;
  loop invariant i <= j + 10;
  loop invariant i % 2 == 1;
  loop invariant 13 <= j;
  loop invariant 12 <= j;
  loop invariant 1 <= i;
  loop assigns j;
  loop assigns i;
  */
  while (j >= i) {
    i  = i + 2;
    j  = j - 1;
  }
  // post-condition
  // @ assert j == 13;
}
