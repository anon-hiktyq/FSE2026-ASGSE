/*@
requires 1 <= n;
*/
/* 2. FUNC CONTRACT */
void foo(int n) {
  int i = 1;
  int sn = 0;
  
  /* 1. LOOP INVARIANT */
  while (i <= n) {
    i  = i + 1;
    sn  = sn + 1;
  }

}
