/*@
requires i == 1;
requires j == 20;
*/
void foo(int i, int j) {
  // loop body
  /*@
  loop invariant i % 2 == 1;
  loop invariant 0 <= j - i;
  loop assigns j;
  loop assigns i;
  */
  while (j >= i) {
    i  = i + 2;
    j  = j - 1;
  }

}
