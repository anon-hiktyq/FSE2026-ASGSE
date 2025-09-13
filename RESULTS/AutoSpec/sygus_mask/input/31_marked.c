/* 2. FUNC CONTRACT */
void foo(int n) {
  int x = n;
  // loop body
  /* 1. LOOP INVARIANT */
  while (x > 1) {
    x  = x - 1;
  }

}
