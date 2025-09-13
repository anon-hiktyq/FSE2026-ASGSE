

void foo032(int b,int j) {
  int k = 100;
  int i = j;
  int n = 0;
  /*@
  loop invariant n % 2 == 1 ==> i - j == (n / 2) + 1;
  loop invariant n % 2 == 1 ==> b == 1;
  loop invariant n % 2 == 0 ? i == j + n/2 : i == j + n/2 + 1;
  loop invariant n % 2 == 0 ==> i - j == (n / 2);
  loop invariant n % 2 == 0 ==> b == 0;
  loop invariant i == j || i == j + 1;
  loop invariant i <= j + n;
  loop invariant i - j == b - j0;
  loop invariant i + j == n + j;
  loop invariant i + j == n + 2*j;
  loop invariant i + j == n + 2*j0;
  loop invariant i + j == n + 2 * j;
  loop invariant i + j == n + 2 * j0;
  loop invariant i + j == j + n;
  loop invariant i + j == 2*n + j - i;
  loop invariant i + j == 100 + n;
  loop invariant b == 0 || b == 1;
  loop invariant \forall integer x; 0 <= x < n ==> ((x % 2 == 1) ==> b == 0);
  loop invariant \forall integer x; 0 <= x < n ==> ((x % 2 == 0) ==> b == 1);
  loop invariant (n % 2 == 1) ==> b == (i != j);
  loop invariant (n % 2 == 0) ==> b == (i == j);
  loop invariant (n % 2 == 0) == (b == 0);
  loop invariant (i - j) % 2 == n % 2;
  loop invariant (b && n % 2 == 0) || (!b && n % 2 == 1);
  loop invariant (b && (i == j + 1)) || (!b && (i == j));
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
