void foo(int x) {
  int lock = 0;
  int y = x + 1;
  
  /* @ >>> INFILL <<< */
  while (x != y) {
    if (unknown()) {
      lock = 1;
      x  = y;
    } else {
      lock = 0;
      x  = y;
      y  = y + 1;
    }
  }

}
