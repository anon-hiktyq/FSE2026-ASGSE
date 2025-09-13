

void foo032(int b,int j) {
  int k = 100;
  int i = j;
  int n = 0;
  /*@
  loop invariant n <= 2*k;;
  loop invariant n % 2 == b;;
  loop invariant n % 2 == b;
  loop invariant j <= i;
  loop invariant i <= j + (n / 2);
  loop invariant i - j == n - (j + i);;
  loop invariant i - j == (n % 2 ? 1 : 0);
  loop invariant i - j == (n % 2 == 1 ? 1 : 0);
  loop invariant i - j == (n % 2 == 0 ? 0 : 1);
  loop invariant i - j == (b ? 1 : -1);
  loop invariant i - j == (b == 1 ? n / 2 + 1 : n / 2);;
  loop invariant i + j == n + j;
  loop invariant i + j == n + j + i;;
  loop invariant i + j == n + j + i - b * 2;;
  loop invariant i + j == n + 2*j_0;;
  loop invariant b == 0 || b == 1;;
  loop invariant b == (n % 2 == 1);;
  loop invariant b == (n % 2 == 0);
  loop invariant \forall integer p; 0 <= p < n ==> b == (p % 2);
  loop invariant \forall integer p; 0 <= p < n ==> (p % 2 == 0 ==> i > j) && (p % 2 == 1 ==> j > i);
  loop invariant \forall integer m; 0 <= m <= n ==> (m % 2 == 0 ==> b != 0) && (m % 2 == 1 ==> b == 0);
  loop invariant \forall integer m; 0 <= m < n ==> m % 2 == 1 ==> b == 1;
  loop invariant \forall integer m; 0 <= m < n ==> m % 2 == 0 ==> b == 0;
  loop invariant \forall integer l; 0 <= l < n ==> l % 2 == (b ? 0 : 1);
  loop invariant 0 <= n;;
  loop invariant (n % 2 == 1) ==> (b == 1);
  loop invariant (n % 2 == 0) ==> (b == 0);
  loop invariant (b == 1) ==> (n % 2 == 1);
  loop invariant (b == 1) ==> (i == j + n / 2);
  loop invariant (b == 1 ==> (i + j == n + i));
  loop invariant (b == 1 && i > j) || (b == 0 && j >= i);
  loop invariant (b == 0) ==> (n % 2 == 0);
  loop invariant (b == 0) ==> (j == i + n / 2);
  loop invariant (b == 0 ==> (i + j == n + j));
  loop invariant n <= 2*k;
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
