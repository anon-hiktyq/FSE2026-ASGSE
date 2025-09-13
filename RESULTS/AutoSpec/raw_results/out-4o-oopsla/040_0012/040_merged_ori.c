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
  loop invariant j % 2 == 1;
  loop invariant j % 2 == 0;
  loop invariant i <= j;
  loop invariant i % 2 == j % 2;
  loop invariant i % 2 == 0;
  loop invariant b == a * (j - i);
  loop invariant b + a * (i - j) == 0;
  loop invariant a == b;
  loop invariant 1 <= j;
  loop invariant 0 <= j;
  loop invariant 0 <= i;
  loop invariant 0 <= b;
  loop invariant 0 <= a;
  loop invariant 0 <= (j - i);
  loop invariant (i % 2) == (j % 2);
  loop invariant (flag == 0) ==> (i % 2 == 1 && j == i);
  loop invariant (flag != 0) ==> i % 2 == 0;
  loop invariant (flag != 0) ==> (i % 2 == 0 && j == i + 1);
  loop assigns j;
  loop assigns i;
  loop assigns b;
  loop assigns a;
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