/*@
requires n >= 0;
*/
/* 2. FUNC CONTRACT */
void foo(int n) {
  int x = n;
  int y = 0;
    
  /* 1. LOOP INVARIANT */
  while (x > 0) {
    y  = y + 1;
    x  = x - 1;
  }

}