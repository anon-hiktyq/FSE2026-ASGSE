/*@
requires i == 1;
requires j == 20;
*/
void foo(int i, int j) {
  // loop body
  /* @ >>> INFILL <<< */
  while (j >= i) {
    i  = i + 2;
    j  = j - 1;
  }

}
