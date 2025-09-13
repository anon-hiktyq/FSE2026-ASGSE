

void foo032(int b,int j) {
  int k = 100;
  int i = j;
  int n = 0;
  /*@
  loop invariant n <= k + j - \at(j, Pre);
  loop invariant n <= k + j - \at(j, Pre) || n <= k + i - \at(i, Pre);
  loop invariant n <= k + j - \at(j, Pre) || i <= j;
  loop invariant n <= k + j - \at(j, Pre) || i <= \at(i, Pre) + n / 2;
  loop invariant n <= k + j - \at(j, Pre) || \at(i, Pre) <= i;
  loop invariant n <= k + j - \at(j, Pre) || \at(i, Pre) + \at(j, Pre) <= i + j;
  loop invariant n <= k + j - \at(j, Pre) || 0 <= n;
  loop invariant n <= k + i - \at(i, Pre);
  loop invariant n < k + j - \at(j, Pre);
  loop invariant n < k + i - \at(i, Pre);
  loop invariant n % 2 == 1 || i >= j;
  loop invariant n % 2 == 0 || j >= i;
  loop invariant n % 2 == (b == \at(b, Pre) ? 0 : 1);
  loop invariant k == 100;;
  loop invariant j - i == n - (\at(j, Pre) - \at(i, Pre));;
  loop invariant j - i == n - (\at(i, Pre) - \at(j, Pre));
  loop invariant j - i == \at(j, Pre) - \at(i, Pre);
  loop invariant i <= j;;
  loop invariant i <= j || n <= k + i - \at(i, Pre);
  loop invariant i <= j || i <= \at(i, Pre) + n / 2;
  loop invariant i <= j || \at(i, Pre) <= i;
  loop invariant i <= \at(i, Pre) + n;
  loop invariant i <= \at(i, Pre) + n || n <= k + j - \at(j, Pre);
  loop invariant i <= \at(i, Pre) + n || n <= k + i - \at(i, Pre);
  loop invariant i <= \at(i, Pre) + n || i <= j;
  loop invariant i <= \at(i, Pre) + n || i <= \at(i, Pre) + n / 2;
  loop invariant i <= \at(i, Pre) + n || \at(i, Pre) <= i;
  loop invariant i <= \at(i, Pre) + n || \at(i, Pre) + \at(j, Pre) <= i + j;
  loop invariant i <= \at(i, Pre) + n || 0 <= n;
  loop invariant i <= \at(i, Pre) + n / 2;
  loop invariant i <= \at(i, Pre) + n / 2 || n <= k + i - \at(i, Pre);
  loop invariant i <= \at(i, Pre) + n / 2 || \at(i, Pre) <= i;
  loop invariant i < j;;
  loop invariant i < \at(i, Pre) + n;
  loop invariant i < \at(i, Pre) + n / 2;
  loop invariant i - j == \at(i, Pre) - \at(j, Pre);
  loop invariant i - \at(i, Pre) + j - \at(j, Pre) == n;;
  loop invariant i + j == \at(i, Pre) + \at(j, Pre) + n;;
  loop invariant i + j == \at(i, Pre) + \at(j, Pre) + n;
  loop invariant i + j == \at(i + j, Pre) + n;
  loop invariant \forall integer x; 0 <= x < n ==> (x % 2 == 0 ? b != \at(b, Pre) : b == \at(b, Pre));
  loop invariant \forall integer m; 0 <= m < n ==> (m % 2 == 1 ==> b != \at(b, Pre));;
  loop invariant \forall integer m; 0 <= m < n ==> (m % 2 == 0 ? b == \at(b, Pre) : b != \at(b, Pre));
  loop invariant \at(i, Pre) <= i;
  loop invariant \at(i, Pre) <= i || n <= k + i - \at(i, Pre);
  loop invariant \at(i, Pre) < i;
  loop invariant \at(i, Pre) + \at(j, Pre) <= i + j;;
  loop invariant \at(i, Pre) + \at(j, Pre) <= i + j || n <= k + i - \at(i, Pre);
  loop invariant \at(i, Pre) + \at(j, Pre) <= i + j || i <= j;
  loop invariant \at(i, Pre) + \at(j, Pre) <= i + j || i <= \at(i, Pre) + n / 2;
  loop invariant \at(i, Pre) + \at(j, Pre) <= i + j || \at(i, Pre) <= i;
  loop invariant \at(i, Pre) + \at(j, Pre) <= i + j || 0 <= n;
  loop invariant \at(i, Pre) + \at(j, Pre) < i + j;;
  loop invariant 0; <= n;
  loop invariant 0; < n;
  loop invariant 0 <= n || n <= k + i - \at(i, Pre);
  loop invariant 0 <= n || i <= j;
  loop invariant 0 <= n || i <= \at(i, Pre) + n / 2;
  loop invariant 0 <= n || \at(i, Pre) <= i;
  loop invariant 0 <= n && n <= 100;
  loop invariant (n % 2 == 1) ==> j == \at(j, Pre);
  loop invariant (n % 2 == 1) ==> b != \at(b, Pre);;
  loop invariant (n % 2 == 0) ==> i == \at(i, Pre);
  loop invariant (n % 2 == 0) ==> b == \at(b, Pre);;
  loop invariant (n % 2 == 0) ==> b == \at(b, Pre);
  loop invariant (n % 2 == 0 && i >= \at(i, Pre)) || (n % 2 == 1 && j >= \at(j, Pre));
  loop invariant (j - i) == (n % 2 == 0 ? (\at(j, Pre) - \at(i, Pre)) : (\at(i, Pre) - \at(j, Pre)));
  loop invariant (b == \at(b, Pre)) ==> (n % 2 == 0);
  loop invariant (b != \at(b, Pre)) ==> (n % 2 == 1);
  loop invariant n <= 2*k;
  loop invariant n <= 2 * k;
  loop invariant j <= \at(j, Pre) + n;
  loop invariant j - \at(j, Pre) <= n;
  loop invariant b == (n % 2 == 0 ? \at(b, Pre) : !\at(b, Pre));
  loop invariant \at(j, Pre) <= j;
  loop invariant 0 <= n;
  loop invariant 0 <= j - \at(j, Pre);
  loop invariant (n % 2 == 1) ==> b != \at(b, Pre);
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
