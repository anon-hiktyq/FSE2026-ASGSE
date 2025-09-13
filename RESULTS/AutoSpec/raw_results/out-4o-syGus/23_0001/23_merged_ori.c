/*@
requires i == 1;
requires j == 20;
*/
void foo(int i, int j) {
  // loop body
  /*@
  loop invariant j <= 20;
  loop invariant i <= j + 8;
  loop invariant i <= j + 2;
  loop invariant i <= j + 20;
  loop invariant i <= 21;
  loop invariant i - 2 <= j;
  loop invariant i - 1 <= j;
  loop invariant i + j == 21;
  loop invariant i % 2 == 1;
  loop invariant 13 <= j;
  loop invariant 1 <= j;
  loop invariant 1 <= i;
  loop invariant 0 <= j;
  loop invariant (j - i) % 2 == 17;
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
