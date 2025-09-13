/*@
requires (x == 100);
*/
/* 2. FUNC CONTRACT */
void foo(int x) { 
  // loop body
  /* 1. LOOP INVARIANT */
  while (x > 0) {
    x  = x - 1;
  }

}
