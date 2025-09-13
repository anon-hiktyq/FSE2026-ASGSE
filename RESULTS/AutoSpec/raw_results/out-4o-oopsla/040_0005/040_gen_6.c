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
  loop invariant 0 <= i;
  loop invariant 0 <= j;
  loop invariant (j - i) % 2 == 1;
  loop invariant i <= j;
  loop invariant i % 2 == 0 || flag == 0;
  loop invariant flag > 0 ==> i % 2 == 0;
  loop invariant ret == 1 ==> i % 2 == 0;
  loop invariant ret == 0 <=> i % 2 == 1;
  loop invariant flag != 0 ==> i % 2 == 0;
  loop invariant flag == 0 ==> j % 2 != 0;
  loop invariant 0 <= i && 0 <= j;
  loop invariant i % 2 == j % 2 || flag < 0;
  loop assigns i, j, flag;
  
  loop invariant 0 <= i;
  loop invariant j >= i;
  loop invariant flag > 0 ==> i % 2 == 0;
  loop invariant flag == 0 ==> j % 2 != 0;
  loop invariant flag != 0 <=> j % 2 == 1;
  loop invariant \forall integer x; x >= 0 ==> (x % 2 == i % 2);
  loop invariant \exists integer x; 0 <= x < j ==> (j - x) % 2 == 0;
  loop assigns a, b, flag;
  loop invariant j % 2 == 1 ==> i % 2 == 0;
  loop invariant j % 2 == 0 ==> i % 2 != 0;
  loop invariant i / 2 <= j;
  loop invariant i % 2 == 1 || i % 2 == 0;
  loop invariant i % 2 == 1 ==> j % 2 == 0;
  loop invariant i % 2 == 0 || i % 2 == 1;
  loop invariant i % 2 == 0 ==> j % 2 == 1;
  loop invariant i % 2 != 0 ==> j % 2 == 0;
  loop invariant flag > 0 ==> i % 2 == 0;
  loop invariant flag == 0 ==> i % 2 == 1;
  loop invariant flag <= 0 ==> i % 2 == 1;
  loop invariant flag <= 0 ==> i % 2 != 0;
  loop invariant \forall integer x; 0 <= x ==> (i % 2 == x % 2) ==> (j % 2 != x % 2);
  loop invariant \forall integer m; m >= 0 ==> j - i + m >= 1;
  loop invariant \forall integer k; 0 <= k < i ==> (k % 2 == 0) ==> (j % 2 == 1);
  loop invariant 1 <= j;
  loop invariant 1 <= j - i;
  loop invariant 0 <= j;
  loop invariant 0 <= i;
  loop invariant 0 < j;
  loop invariant (i % 2 == 1 ==> j % 2 == 0);
  loop invariant (i % 2 == 0) ==> (j % 2 == 1);
  loop invariant (i % 2 == 0) ==> (j % 2 != 0);
  loop invariant (i % 2 == 0 ==> j % 2 == 1);
  loop invariant (i % 2 != 0) ==> (j % 2 == 0);
  loop invariant (i % 2 != 0) ==> (j % 2 != 0);
  loop invariant (flag == 0) ==> i % 2 == 1;
  loop invariant (flag == 0) ==> (i % 2 == 1);
  loop invariant (flag == 0 ==> i % 2 == 1);
  loop invariant (flag != 0) ==> i % 2 == 0;
  loop invariant (flag != 0) ==> (i % 2 == 0);
  loop invariant (flag != 0 ==> i % 2 == 0);
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
  loop invariant i <= j;
  loop invariant i < j;
  loop invariant flag > 0 ==> i % 2 == 0;
  loop invariant flag > 0 ==> b >= a * (j - i);
  loop invariant flag > 0 ==> (i % 2 == 0);
  loop invariant flag == 0 ==> (i % 2 == 1);
  loop invariant flag <= 0 ==> i % 2 != 0;
  loop invariant flag <= 0 ==> b % (j - i) == 0;
  loop invariant b == a * (j - i);
  loop invariant a * (j - i) == b;
  loop invariant \forall integer x; x >= 0 ==> (b - a * (j - i) == 0);
  loop invariant \forall integer k; 0 <= k <= a ==> b >= k * (j - i);
  loop invariant \exists integer k; 0 <= k <= a && b == k * (j - i);
  loop invariant 1 <= j;
  loop invariant 0 <= j - i;
  loop invariant 0 <= i;
  loop invariant 0 <= b;
  loop invariant 0 <= a;
  loop invariant 0 <= (j - i);
  loop invariant 0 < j;
  loop invariant 0 < (j - i);
  loop invariant (flag > 0) ==> (i % 2 == 0);
  loop invariant (flag > 0) ==> (b == a * (j - i));
  loop invariant (flag > 0) ==> ((i % 2 == 0) && (j > i));
  loop invariant (flag == 0) ==> (i % 2 == 1);
  loop invariant (flag == 0) ==> (b == a * (j - i));
  loop invariant (flag == 0) ==> ((i % 2 == 1) && (b == a * (j - i)));
  loop invariant (flag != 0) ==> (i % 2 == 0);
  loop invariant (flag != 0) ==> (b == a * (j - i));
  loop invariant (b == 0) ==> (a == 0);
  loop assigns b;
  loop assigns a;
  */
  while (unknown2()) {
    a++;
    b += (j - i);
  }
  // @ assert (flag!= 0) ==> (a==b);
}