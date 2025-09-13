/*@
requires n > 0;
*/
/* 2. FUNC CONTRACT */
void foo(int n) {
  int c = 0;

  /* 1. LOOP INVARIANT */
  while (unknown()) {
    if (unknown()) {
      if (c != n) {
        c = c + 1;
      }
    } else {
      if (c == n)
      {
        c = 1;
      }
    }
  }

}
