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
  loop invariant ret == 1 ==> i % 2 == 0;
  loop invariant ret == 0 <=> i % 2 == 1;
  loop invariant j % 2 == 0 || j % 2 == 1;
  loop invariant i <= j;
  loop invariant i <= j;
  loop invariant i <= j || i < j;
  loop invariant i <= j || a <= b;
  loop invariant i <= j || 0 <= a;
  loop invariant i < j;
  loop invariant i < j;
  loop invariant i < j || 0 <= a;
  loop invariant i % 2 == j % 2 || flag < 0;
  loop invariant i % 2 == 0 || i % 2 != 0;
  loop invariant i % 2 == 0 || flag == 0;
  loop invariant flag > 0 ==> b >= a * (j - i);
  loop invariant flag > 0 ==> ((i % 2 == 0) && (j > i));
  loop invariant flag == 0 ==> j % 2 != 0;
  loop invariant flag != 0 ==> i % 2 == 0;
  loop invariant flag != 0 <=> j % 2 == 1;
  loop invariant b == a * (j - i);
  loop invariant a == 0 || b % (j - i) == 0;
  loop invariant a <= b;
  loop invariant a <= b || i < j;
  loop invariant a <= b || 0 <= a;
  loop invariant a < b;
  loop invariant a * (j - i) == b;
  loop invariant \forall integer z; 0 <= z && z == a ==> b >= z*(j-i);
  loop invariant \forall integer x; x >= 0 ==> b == a * (j - i);
  loop invariant \forall integer x; x >= 0 ==> (x % 2 == i % 2);
  loop invariant \forall integer x; x >= 0 ==> (b == a * (j - i));
  loop invariant \forall integer x; x >= 0 ==> (b - a * (j - i) == 0);
  loop invariant \forall integer x; 0 <= x ==> x*(j-i) <= b;
  loop invariant \forall integer x; 0 <= x ==> i % 2 == 0 || i % 2 != 0;
  loop invariant \forall integer x; 0 <= x ==> (i % 2 != x % 2) ==> (j % 2 == x % 2);
  loop invariant \forall integer m; m >= 1 ==> i <= j + m;
  loop invariant \forall integer k; 0 <= k <= a ==> b >= k * (j - i);
  loop invariant \forall integer k; 0 <= k < i ==> k % 2 == i % 2;
  loop invariant \forall integer k; 0 <= k < i ==> k % 2 == 1;
  loop invariant \forall integer k; 0 <= k < i ==> j % 2 != 0;
  loop invariant \forall integer k; 0 <= k < i ==> 2*k <= i;
  loop invariant \exists integer z; 0 <= z <= a && b == z*(j-i);
  loop invariant \exists integer x; 0 <= x < j ==> (j - x) % 2 == 0;
  loop invariant \exists integer x; 0 <= x && (x % 2 == i % 2);
  loop invariant \exists integer k; 0 <= k <= j && i % 2 == 0;
  loop invariant \exists integer k; 0 <= k <= a && b == k * (j - i);
  loop invariant \exists integer k; 0 <= k && b == k * (j - i);
  loop invariant 0 <= j - i;
  loop invariant 0 <= j - i;
  loop invariant 0 <= j - i || i <= j;
  loop invariant 0 <= j - i || i < j;
  loop invariant 0 <= j - i || a <= b;
  loop invariant 0 <= j - i || 0 <= a;
  loop invariant 0 <= i && 0 <= j;
  loop invariant 0 <= b;
  loop invariant 0 <= b || i <= j;
  loop invariant 0 <= b || i < j;
  loop invariant 0 <= b || a <= b;
  loop invariant 0 <= b || 0 <= j - i;
  loop invariant 0 <= b || 0 <= a;
  loop invariant 0 <= b || 0 < j - i;
  loop invariant 0 <= a;
  loop invariant 0 < j - i;
  loop invariant 0 < j - i;
  loop invariant 0 < j - i || i <= j;
  loop invariant 0 < j - i || i < j;
  loop invariant 0 < j - i || a <= b;
  loop invariant 0 < j - i || 0 <= j - i;
  loop invariant 0 < j - i || 0 <= a;
  loop invariant 0 < b;
  loop invariant 0 < a;
  loop invariant (j - i) % 2 == 1;
  loop invariant (i % 2 == 1) ==> (j % 2 == 0);
  loop invariant (flag > 0) ==> i % 2 == 0;
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