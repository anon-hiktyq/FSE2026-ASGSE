
void foo58() {

  int w = 1;
  int z = 0;
  int x = 0;
  int y = 0;

  /* Store initial values before the loop */
  int initial_w = w;
  int initial_z = z;
  int initial_x = x;
  int initial_y = y;

  /* >>> LOOP INVARIANT TO FILL <<< */
  /*@
    loop invariant (w == 0 || w == 1); // PLACE_HOLDER_w
    loop invariant (z == 0 || z == 1); // PLACE_HOLDER_z
    loop assigns x, y, w, z;
    loop variant x + y; // Correct variant function ensuring termination
  */
  while(unknown()) {
    if(w) {
      x++;
      w = !w;
    }

    if(!z) {
      y++;
      z = !z;
    }
  }
    /*@ assert x == y; */

  /* mask_1 */
}
