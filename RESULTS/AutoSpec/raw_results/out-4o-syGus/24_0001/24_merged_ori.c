/*@
requires i == 1;
requires j == 20;
*/
void foo(int i, int j) {
  // loop body
  /*@
  loop invariant j <= 20;
  loop invariant i == 2*(10-j) + 1;
  loop invariant i == 1 + 2*(20 - j);
  loop invariant i <= j+2;
  loop invariant i <= j + 2;
  loop invariant i <= j + 1;
  loop invariant i <= j + 19;
  loop invariant i <= 21;
  loop invariant i + j <= 22;
  loop invariant i % 2 == 1;
  loop invariant 6 <= j;
  loop invariant 21 <= i + j;
  loop invariant 1 <= i;
  loop invariant (j - i) % 2 == 17;
  loop invariant (j - i) % 2 == 16;
  loop invariant (j - i) % 2 == 0;
  loop invariant (j - 6) + 2*(i - 1)/2 == 19;
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
