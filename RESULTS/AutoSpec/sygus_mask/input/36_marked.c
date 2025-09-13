int unknown();

/* 2. FUNC CONTRACT */
int main() {
  int c = 0;

  /* 1. LOOP INVARIANT */
  while (unknown()) {
    if (unknown()) {
      if (c != 40) {
        c  = c + 1;
      }
    } else {
      if (c == 40) {
        c  = 1;
      }
    }
  }

}
