/*@
requires size >= 1;
*/
/* 2. FUNC CONTRACT */
void foo(int size) {
  int i = 1;
  int sn = 0;
  
  /* 1. LOOP INVARIANT */
  while (i <= size) {
    i = i + 1;
    sn = sn + 1;
  }

}
