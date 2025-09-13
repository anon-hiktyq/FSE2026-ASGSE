int unknown1();
int unknown2();

/*@
requires flag > 0;
*/
void foo040(int flag) {
  int i, j, k;
  j = 1;
  if (flag) {
    i = 0;
  } else {
    i = 1;
  }

  /*@
  loop invariant i % 2 == 0;
  loop invariant j % 2 == 1;
  loop invariant j >= 1;
  loop assigns i, j;
  
  loop invariant a >= 0;
  loop invariant b == a * (j - i);
  loop assigns a, b;
  */
  while (unknown1()) {
    i += 2;
    if (i % 2 == 0) {
      j += 2;
    } else j++;
  }

  int a = 0;
  int b = 0;

  while (unknown2()) {
    a++;
    b += (j - i);
  }
  // @ assert (flag!= 0) ==> (a==b);
}