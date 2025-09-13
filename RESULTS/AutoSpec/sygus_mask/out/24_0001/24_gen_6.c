/*@
requires i == 1;
requires j == 20;
*/
void foo(int i, int j) {
  // loop body
  /*@
  loop invariant j >= i;
  loop invariant i >= 1;
  loop invariant j == 20 - (i - 1) / 2; // Assuming i increments by 2 each iteration
  loop assigns i;
  loop assigns j;
  */
  while (j >= i) {
    i  = i + 2;
    j  = j - 1;
  }

}
