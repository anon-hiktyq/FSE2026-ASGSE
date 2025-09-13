/*@
requires n >= 0;
*/
/* 2. FUNC CONTRACT */
void foo(int n) {
  int x = 0;

  /* 1. LOOP INVARIANT */
  while (x < n) {
    x  = x + 1;
  }

}
