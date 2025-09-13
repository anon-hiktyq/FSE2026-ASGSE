
void foo54(int x, int y) {
  x = -50;

  /* >>> LOOP INVARIANT TO FILL <<< */
  /*@
    loop invariant \at(y, Pre) <= y;
  */
  while (x < 0) {
    x = x + y;
    y++;
  }
    /*@ assert y > 0;*/
}
