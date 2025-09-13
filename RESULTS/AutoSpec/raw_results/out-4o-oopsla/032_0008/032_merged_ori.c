

void foo032(int b,int j) {
  int k = 100;
  int i = j;
  int n = 0;
  /*@
  loop invariant n % 2 == b == (\at(b, Pre) && n % 2 == 0 || !\at(b, Pre) && n % 2 == 1);
  loop invariant n % 2 == (b ? 0 : 1);
  loop invariant n % 2 == (\at(b, Pre) ? 1 : 0);
  loop invariant j <= \at(j, Pre) + n;
  loop invariant j - \at(j, Pre) <= n;
  loop invariant i <= \at(i, Pre) + n;
  loop invariant i - j == \at(j, Pre) - \at(i, Pre);
  loop invariant i - j == \at(i, Pre) - \at(j, Pre);
  loop invariant i - \at(i, Pre) <= n;
  loop invariant i + j == n + \at(j, Pre);;
  loop invariant i + j == \at(i, Pre) + \at(j, Pre) + n;;
  loop invariant i + j == \at(i, Pre) + \at(j, Pre) + n;
  loop invariant \forall integer x; 0 <= x <= n ==> (x % 2 == 1 ==> b != \at(b, Pre));
  loop invariant \forall integer x; 0 <= x <= n ==> (x % 2 == 0 ==> b == \at(b, Pre));
  loop invariant \forall integer x; 0 <= x < n ==> (x % 2 == 1 ==> j == \at(j, Pre) + x/2 + 1);
  loop invariant \forall integer x; 0 <= x < n ==> (x % 2 == 0 ==> i == \at(i, Pre) + x/2);
  loop invariant \forall integer m; 0 <= m <= n ==> (m % 2 == 0 ? b == \at(b, Pre) : b != \at(b, Pre));
  loop invariant \forall integer m; 0 <= m < n ==> m % 2 == 1 ==> b == \at(b, Pre);
  loop invariant \forall integer m; 0 <= m < n ==> m % 2 == 0 ==> b == !\at(b, Pre);
  loop invariant \forall integer m; 0 <= m < n ==> i + j == \at(i, Pre) + \at(j, Pre) + m;
  loop invariant \forall integer m; 0 <= m < n ==> (m % 2 == 0 ? b == \at(b, Pre) : b != \at(b, Pre));;
  loop invariant \at(j, Pre) <= j;
  loop invariant \at(i, Pre) <= i;
  loop invariant 0 <= j - \at(j, Pre);
  loop invariant 0 <= i - \at(i, Pre);
  loop invariant (n % 2 == 1) ==> j == \at(j, Pre) + (n+1)/2;
  loop invariant (n % 2 == 1) ==> b != \at(b, Pre);
  loop invariant (n % 2 == 0) ==> i == \at(i, Pre) + n/2;
  loop invariant (n % 2 == 0) ==> b == \at(b, Pre);
  loop invariant n <= 2*k;
  loop invariant n <= 2 * k;
  loop invariant b == (n % 2 == 0 ? \at(b, Pre) : !\at(b, Pre));
  loop invariant 0 <= n;
  loop assigns n;
  loop assigns j;
  loop assigns i;
  loop assigns b;
  */
  for( n = 0 ; n < 2*k ; n++ ) {
    if(b) {
      i++;
    } else {
      j++;
    }
    b = !b;
  }
  // @ assert i ==j;
}
