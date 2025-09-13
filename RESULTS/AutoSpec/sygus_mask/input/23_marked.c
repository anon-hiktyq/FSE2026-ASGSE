/*@
requires i == 1;
requires j == 20;
*/
/* 2. FUNC CONTRACT */
void foo(int i, int j) {
  // loop body
  /* 1. LOOP INVARIANT */
  while (j >= i) {
    i  = i + 2;
    j  = j - 1;
  }

}
