/*@
requires i == 1;
requires j == 20;
*/
void foo(int i, int j) {
  // loop body
  /*@
  loop invariant j == 21 - i;
  loop invariant j <= 20;
  loop invariant i == 21 - (j - 6);
  loop invariant i == 21 - (j - 5);
  loop invariant i <= j + 3;
  loop invariant i <= j + 2;
  loop invariant i <= 21;
  loop invariant i <= 20;
  loop invariant i - 2 <= j;
  loop invariant i - 1 <= j;
  loop invariant i % 2 == 1;
  loop invariant 6 <= j;
  loop invariant 1 <= i;
  loop invariant (j - i) % 3 == 2;
  loop assigns j;
  loop assigns i;
  */
  while (j >= i) {
    i  = i + 2;
    j  = j - 1;
  }
  // post-condition
  // @ assert j == 6;
}
