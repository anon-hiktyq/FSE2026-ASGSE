

void foo032(int b,int j) {
  int k = 100;
  int i = j;
  int n = 0;
  /*@
  loop invariant i - j == \abs(i - j);
  loop invariant i + j == n + j;
  loop invariant i + j == n + j + i;;
  loop invariant i + j == n + j + i;
  loop invariant i + j == n + 2 * j_initial;
  loop invariant i + j == n + 2 * j0;;
  loop invariant i + j == j0 + n;;
  loop invariant i + j == j + i + n;
  loop invariant i + j == 2 * n + j;;
  loop invariant b == 0 || b == 1;
  loop invariant b == (n % 2 == 1);
  loop invariant b == (n % 2 == 0);
  loop invariant \forall integer p; 0 <= p < n ==> (b_initial ? p % 2 == 1 : p % 2 == 0);
  loop invariant \forall integer p; 0 <= p < n ==> ((p % 2 == 0) ==> b == 1) && ((p % 2 != 0) ==> b == 0);
  loop invariant \forall integer m; 0 <= m <= n ==> (b ? i == j0 + m : j == j0 + m);
  loop invariant \forall integer m; 0 <= m < n ==> (m % 2 == 0 ==> i == j + m / 2);
  loop invariant \exists integer m; 0 <= m <= n && (m % 2 == 0 ==> b == 1) && (m % 2 == 1 ==> b == 0);;
  loop invariant 0 <= j;
  loop invariant 0 <= i;
  loop invariant (n % 2 == 1) ==> (b == 1);
  loop invariant (n % 2 == 0) ==> (b == 0);;
  loop invariant (n % 2 == 0 ==> b == 1) && (n % 2 == 1 ==> b == 0);
  loop invariant (n % 2 == 0 ==> b == 0) && (n % 2 == 1 ==> b == 1);
  loop invariant (i == j + (n / 2)) || (j == i + (n / 2));
  loop invariant (b == 1) ==> (i == j + n/2 + 1);;
  loop invariant (b == 0) ==> (j == i + n/2 - 1);
  loop invariant (b == 0 || b == 1);
  loop invariant (b == 0 ==> i == j + n) && (b == 1 ==> j == i + n);
  loop invariant n <= 2 * k;
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
