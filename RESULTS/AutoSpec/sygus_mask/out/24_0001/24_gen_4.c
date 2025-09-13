/*@
requires i == 1;
requires j == 20;
*/
void foo(int i, int j) {
  // loop body
  /*@
  loop invariant i >= 1;
  loop invariant j >= 20;
  loop invariant j - i >= 20 - 1; // j - i is always at least 19 initially
  loop invariant j >= i; 
  loop assigns i;
  loop assigns j;
  */
  while (j >= i) {
    i  = i + 2;
    j  = j - 1;
  }

}
