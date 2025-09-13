/*@
requires n >= 0;
requires k >= 0;
*/
/* 2. FUNC CONTRACT */
void foo(int k, int n) {
  int i = 0;
  int j = 0;
  
  /* 1. LOOP INVARIANT */
  while (i <= n) {
    i  = i + 1;
    j  = j + i;
  }

}
