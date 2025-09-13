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
  loop invariant (i % 2) == (j % 2);
  loop invariant 0 <= i;
  loop invariant 0 <= j;
  loop assigns i, j;
  
  loop invariant a == b;
  loop invariant 0 <= a;
  loop invariant 0 <= b;
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