
/*@
    requires flag > 0;
    */
void foo69(int flag) {
  int i, j, k;
  j = 1;
  if (flag) {
    i = 0;
  } else {
    i = 1;
  }

  /*@
    loop invariant i >= 0;
    loop invariant j >= 1;
    loop invariant j >= 1 + i / 2;
    loop invariant flag == \at(flag,Pre);
    loop variant i;
    */
  while (unknown1()) {
    i += 2;
    if (i % 2 == 0) {
      j += 2;
    } else j++;
  }

  int a = 0;
  int b = 0;

  /*@
    loop invariant a >= 0;
    loop invariant b == a * (j - i);
    loop invariant j >= 1;
    loop variant a;
    */
  while (unknown2()) {
    a++;
    b += (j - i);
  }
  /* mask_1 */
}
