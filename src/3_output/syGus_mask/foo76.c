
/*@
    requires 0 <= y && y <= 127;
    */
    
void foo76(int y, int x1, int x2, int x3) {
  int c = 0;
  int z = 36 * y;
  
  /*@
      loop invariant (\at(y, Pre) >= 0 && \at(y, Pre) <= 127) ==> (0 <= c <= 36);
      loop invariant (\at(y, Pre) >= 0 && \at(y, Pre) <= 127) ==> (z == 36 * y + c);
      loop invariant (\at(y, Pre) >= 0 && \at(y, Pre) <= 127) ==> (x3 == \at(x3, Pre));
      loop invariant (\at(y, Pre) >= 0 && \at(y, Pre) <= 127) ==> (x2 == \at(x2, Pre));
      loop invariant (\at(y, Pre) >= 0 && \at(y, Pre) <= 127) ==> (x1 == \at(x1, Pre));
      loop invariant (\at(y, Pre) >= 0 && \at(y, Pre) <= 127) ==> (y == \at(y, Pre));
      loop assigns c, z;
  */
  while (unknown()) {
    if (c < 36) {
      z = z + 1;
      c = c + 1;
    }
  }
}
