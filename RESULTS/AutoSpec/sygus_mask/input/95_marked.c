/* 2. FUNC CONTRACT */
void foo(int x) {
  int i = 0;
  int j = 0;
  int y = 0;
  
  /* 1. LOOP INVARIANT */
  while (i <= x) {
    i  = i + 1;
    j  = j + y;
  }

}
