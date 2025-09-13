/*@
requires x == y;
*/
/* 2. FUNC CONTRACT */
void foo(int x, int y) {
  int lock = 1;
  
  /* 1. LOOP INVARIANT */
  while (x != y) {  
    if (unknown()) {
      lock = 1;
      x = y;
    } else {
      lock  = 0;
      x  = y;
      y  = y + 1; 
    }
  }

}
