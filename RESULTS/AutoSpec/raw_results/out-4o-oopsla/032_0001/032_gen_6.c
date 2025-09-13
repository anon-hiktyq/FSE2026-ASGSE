

void foo032(int b,int j) {
  int k = 100;
  int i = j;
  int n = 0;
  /*@
  loop invariant 0 <= n <= 2 * k;
  loop invariant i + j == 2 * j_0 + n;
  loop invariant (n % 2 == 0 && b == b_0) || (n % 2 == 1 && b != b_0);
  loop invariant \forall integer m; 0 <= m < n ==> ((m % 2 == 0 && b_0) || (m % 2 == 1 && !b_0)) ==> i == j_0 + m / 2;
  loop invariant \forall integer m; 0 <= m < n ==> ((m % 2 == 0 && !b_0) || (m % 2 == 1 && b_0)) ==> j == j_0 + m / 2;
  loop assigns n, i, j, b;
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
