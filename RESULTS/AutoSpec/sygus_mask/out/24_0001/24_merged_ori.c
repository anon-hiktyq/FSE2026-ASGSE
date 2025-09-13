/*@
requires i == 1;
requires j == 20;
*/
void foo(int i, int j) {
  // loop body
  /*@
  loop invariant j_initial == 20;
  loop invariant j0 == j + (j0 - j);
  loop invariant j == 20 - (k - 1);
  loop invariant j == 20 - (i - 1) / 2; // Assuming i increments by 2 each iteration;
  loop invariant j <= j_initial;
  loop invariant j <= 20;
  loop invariant j - i == 20 - (j - i);
  loop invariant i; <= j;
  loop invariant i == 1 + 2 * (n - j);
  loop invariant i == 1 + 2 * (k - 1);
  loop invariant i == 1 + 2 * (j_initial - j);
  loop invariant i == 1 + 2 * (j0 - j);
  loop invariant i <= j;
  loop invariant 20 <= j;
  loop invariant 20 - 1; // j - i is always at least 19 initially <= j - i;
  loop invariant 19 <= j - i;
  loop invariant 1 <= k;
  loop invariant 1 <= j;
  loop invariant 1 <= i;
  loop invariant 0 <= j;
  loop assigns j;
  loop assigns i;
  */
  while (j >= i) {
    i  = i + 2;
    j  = j - 1;
  }

}
