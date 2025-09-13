/* 2. FUNC CONTRACT */
int main() {
  int x = -50;
  int y = 0;
  
  /* 1. LOOP INVARIANT */
  while (x < 0) {
    x  = x + y;
    y  = y + 1;
  }

}
