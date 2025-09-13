

void foo032(int b,int j) {
  int k = 100;
  int i = j;
  int n = 0;
  /*@
  loop invariant n <= 2*k;
  loop invariant n <= 2 * k;
  loop invariant n % 2 == (b ? 0 : 1);
  loop invariant i + j == 2*j_0 + n;
  loop invariant i + j == 2 * k + 2 * j_initial;
  loop invariant i + j == 2 * k + 2 * j_0;
  loop invariant i + j == 2 * k + 2 * j;
  loop invariant i + j == 2 * k + 2 * (i - j);
  loop invariant i + j == 2 * j_0 + n; // where j_0 is the initial value of `j`;
  loop invariant i + j == 2 * j_0 + n;
  loop invariant \forall integer m; 0 <= m < n ==> ((m % 2 == 0 && b_0) || (m % 2 == 1 && !b_0)) ==> i == j_0 + m / 2;
  loop invariant \forall integer m; 0 <= m < n ==> ((m % 2 == 0 && !b_0) || (m % 2 == 1 && b_0)) ==> j == j_0 + m / 2;
  loop invariant 0 <= n;
  loop invariant (n % 2 == 0) ? (b == b_0) : (b != b_0);
  loop invariant (n % 2 == 0 && i == j + n / 2) || (n % 2 == 1 && i == j + n / 2 + 1);
  loop invariant (n % 2 == 0 && b == b_0) || (n % 2 == 1 && b != b_0);
  loop invariant (b == 1) ==> (i == j + 1);
  loop invariant (b == 0) ==> (i == j - 1);
  loop invariant (b && i == j_0 + n / 2 + 1) || (!b && i == j_0 + n / 2);
  loop invariant (b && (i - j == (n + 1) / 2)) || (!b && (i - j == -n / 2));
  loop invariant (!b && j == j_0 + n / 2) || (b && j == j_0 + n / 2 - 1);
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
