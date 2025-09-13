/* 2. FUNC CONTRACT */
void foo(int y) {
  int x = 1;
  
  /* 1. LOOP INVARIANT */
  while (x < y) {
    x = x + x;
  }

}
