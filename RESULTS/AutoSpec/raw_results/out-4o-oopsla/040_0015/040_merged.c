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
  loop invariant i % 2 == 1 ==> j % 2 == 1;
  loop invariant i % 2 != 0 ==> j % 2 != 0;
  loop invariant \forall integer k; 0 <= k <= i ==> (k % 2 == 0 ==> j >= k / 2 + 1);
  loop invariant \exists integer n; n >= 0 && i == 2 * n;
  loop invariant 1 <= j;
  loop invariant 0 <= i;
  loop invariant 0 < flag;
  loop assigns j;
  loop assigns i;
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
  loop invariant b == a * (j - i);
  loop invariant 1 <= j;
  loop invariant 0 <= i;
  loop invariant 0 <= a;
  loop invariant 0 < flag;
  loop assigns b;
  loop assigns a;
  */
  while (unknown2()) {
    a++;
    b += (j - i);
  }
  //@ assert (flag!= 0) ==> (a==b);
}