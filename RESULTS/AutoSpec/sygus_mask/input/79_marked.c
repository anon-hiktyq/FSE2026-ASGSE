/*@
requires x >= 0;
requires y >= 0;
requires x >= y;
*/
/* 2. FUNC CONTRACT */
void foo(int x, int y) {
  int i = 0;

  /* 1. LOOP INVARIANT */
  while (unknown()) {
    if (i < y)
    {
      i = i + 1;
    }

  }

}
