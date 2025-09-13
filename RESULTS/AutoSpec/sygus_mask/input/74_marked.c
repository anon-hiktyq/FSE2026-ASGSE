/*@
requires y >= 127;
*/
/* 2. FUNC CONTRACT */
void foo(int y) {
  int c = 0;
  int z = 36 * y;
  
  /* 1. LOOP INVARIANT */
  while (unknown()) {
    if(c < 36)
    {
      z = z + 1;
      c = c + 1;
    }
  }

}
