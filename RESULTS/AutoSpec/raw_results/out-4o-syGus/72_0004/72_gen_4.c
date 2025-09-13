/*@
requires y >= 127;
*/
void foo(int y) {
  int c = 0;
  int z = 36 * y;
  
  /*@
  loop invariant z == 36 * y + c;
  loop invariant c >= 36 ==> z == 36 * y + 36;
  loop invariant c <= 36;
  loop invariant c < 36 ==> z < 36 * y + 36;
  loop invariant z >= 36 * y;
  loop invariant c <= z - 36 * y;
  loop invariant \forall integer k; 0 <= k <= c ==> z >= 36 * y + k;
  loop invariant 127 <= y;
  loop invariant 0 <= c;
  loop invariant z == 36 * y + c;
  loop invariant c >= 36 ==> z == 36 * y + 36;
  loop invariant c <= 36;
  loop invariant c < 36 ==> z < 36 * y + 36;
  loop invariant \forall integer k; 0 <= k < c ==> z > 36 * y;
  loop invariant 127 <= y;
  loop invariant 0 <= c;
  loop assigns z;
  loop assigns c;
  */
  while (unknown()) {
    if (c < 36)
    {
      z = z + 1;
      c = c + 1;
    }
  }
  // post-condition
  if(c < 36) {
    // @ assert z < 4608;
  }
}
