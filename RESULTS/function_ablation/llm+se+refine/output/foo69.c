
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
    loop invariant flag == \at(flag,Pre);
    loop assigns i, j;
    loop variant i; // i is strictly increasing, hence valid as a variant
  */
  while (unknown1()) {
    i += 2;
    if (i % 2 == 0) {
      j += 2;
    } else {
      j++;
    }
  }

  int a = 0;
  int b = 0;

  /*@
    loop invariant a >= 0;
    loop invariant b == a * (j - i);
    loop invariant flag == \at(flag,Pre);
    loop assigns a, b;
    loop variant a; // a is strictly increasing, hence valid as a variant
  */
  while (unknown2()) {
    a++;
    b += (j - i);
  }

  /*@ assert (flag != 0) ==> (b == a * (j - i)); */ // Strengthened invariant ensures postcondition validity
}
