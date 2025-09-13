/* 2. FUNC CONTRACT */
void foo(int x, int y) {
  int i = x;
  int j = y;
  
  /* 1. LOOP INVARIANT */
  while (x != 0) {
    x = x - 1;
    y = y - 1;
  }

}
