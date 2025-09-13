/*@
requires n > 0;
*/
void foo(int n) {
  int c = 0;
  
  /* @ >>> INFILL <<< */
  while (unknown()) {
    if (unknown()) {
      if (c != n) {
        c = c + 1;
      }
    } else {
      if (c == n) {
        c = 1;
      }
    }
  }

}
