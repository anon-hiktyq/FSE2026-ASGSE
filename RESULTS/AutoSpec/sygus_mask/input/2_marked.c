/* 2. FUNC CONTRACT */
void main() {
  // variable declarations
  int x;
  int y;
  // pre-conditions
  x = 1;
  y = 0;
  // loop body
  /* 1. LOOP INVARIANT */
  while (y < 1000) {
    x  = (x + y);
    y  = (y + 1);
  }

}
