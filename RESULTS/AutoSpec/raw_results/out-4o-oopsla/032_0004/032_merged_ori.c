

void foo032(int b,int j) {
  int k = 100;
  int i = j;
  int n = 0;
  /*@
  loop invariant n == 2 * ((i - j) / 2) + ((i - j) % 2 == n % 2 ? 0 : 1);
  loop invariant n <= 2*k;
  loop invariant n % 2 == 1 ==> b != b_0;
  loop invariant n % 2 == 0 ==> b == b_0;
  loop invariant j <= i;
  loop invariant j - i == ((n % 2 == 0) ? 0 : 1);
  loop invariant i - j == n * (2*b - 1);
  loop invariant i - j == n % 2;
  loop invariant i - j == b;
  loop invariant i - j == (n % 2 == 1 ? 1 : 0);
  loop invariant i + j == n + j;
  loop invariant i + j == n + j + b;
  loop invariant i + j == n + 2*j_0;
  loop invariant i + j == n + 2 * j;
  loop invariant i + j == n + 2 * j0;
  loop invariant i + j == j + i;
  loop invariant i + j <= 2*k;
  loop invariant b == (n % 2 == 1);
  loop invariant 0 <= i + j;
  loop invariant (n % 2 == 0 && i == j + n/2) || (n % 2 == 1 && i == j + n/2);
  loop invariant (b == 1) ==> (i == j + n/2);
  loop invariant (b == 1) == (n % 2 == 1);
  loop invariant (b == 0) ==> (i == j + n/2 + (n % 2));
  loop invariant (b == 0) == (n % 2 == 0);
  loop invariant (b == 0 && n % 2 == 0) || (b == 1 && n % 2 == 1);
  loop invariant (b && i == j + 1) || (!b && i == j);
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
