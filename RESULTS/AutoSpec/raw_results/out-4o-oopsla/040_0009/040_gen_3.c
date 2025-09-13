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
  loop invariant j >= 2 || i == 0;
  loop invariant j >= 1 && i >= 0;
  loop invariant j % 2 == 0 || j % 2 == 1;
  loop invariant i + 1 <= j;
  loop invariant i % 2 == 1 ==> j % 2 == 1;
  loop invariant i % 2 == 1 ==> j % 2 == 0;
  loop invariant i % 2 == 0;
  loop invariant i % 2 == 0 || i % 2 == 1;
  loop invariant i % 2 == 0 ==> j % 2 == 1;
  loop invariant i % 2 == 0 ==> flag != 0;
  loop invariant i % 2 != 0 ==> j % 2 != 0;
  loop invariant flag > 0 ==> i % 2 == 0;
  loop invariant \forall integer x; x >= 0 ==> j > i;
  loop invariant \forall integer x; x >= 0 ==> i >= 0 && j >= 1;
  loop invariant \forall integer x; x >= 0 ==> (i + 2 * x) % 2 == 0 || (i + 2 * x) % 2 == 1;
  loop invariant \forall integer x; i >= 0 && j >= 1;
  loop invariant \forall integer x; i >= 0 && j >= 0;
  loop invariant \forall integer x; 0 <= x <= i ==> j >= 1;
  loop invariant \forall integer k; 0 <= k <= i ==> j >= 1;
  loop invariant \exists integer x; x >= 0 && flag > 0;
  loop invariant 1 <= j;
  loop invariant 0 <= i;
  loop invariant 0 < j;
  loop invariant 0 < flag;
  loop invariant (i % 2 == 1) ==> (j >= 2);
  loop invariant (i % 2 == 1) ==> (j % 2 == 0);
  loop invariant (i % 2 == 1) ==> (j % 2 != 0);
  loop invariant (i % 2 == 1 ==> j >= 2);
  loop invariant (i % 2 == 0) ==> (j >= 1);
  loop invariant (i % 2 == 0) ==> (j % 2 == 1);
  loop invariant (i % 2 == 0 ==> j >= 1);
  loop invariant (flag > 0) ==> i % 2 == 0;
  loop invariant (flag != 0) ==> (i % 2 == 0);
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
  loop invariant a >= 0;
  loop invariant b >= 0;
  loop invariant b == a * (j - i);
  loop invariant j >= 1;
  loop invariant i >= 0;
  loop invariant flag > 0;
  loop invariant b % (j - i) == 0;
  loop invariant a == b / (j - i);
  loop invariant \forall integer k; 0 <= k <= a ==> b == k * (j - i);
  loop invariant j >= 1 && i >= 0;
  loop invariant b == a * (j - i);
  loop invariant \forall integer x; a >= 0 && b == a * (j - i);
  loop invariant 1 <= j;
  loop invariant 0 <= i;
  loop invariant 0 <= a;
  loop invariant 0 < flag;
  loop invariant (flag != 0) ==> (i % 2 == 0);
  loop invariant (flag != 0) ==> (b == a * (j - i));
  loop assigns b;
  loop assigns a;
  */
  while (unknown2()) {
    a++;
    b += (j - i);
  }
  // @ assert (flag!= 0) ==> (a==b);
}