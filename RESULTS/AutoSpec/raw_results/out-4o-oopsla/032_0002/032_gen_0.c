

void foo032(int b,int j) {
  int k = 100;
  int i = j;
  int n = 0;
  /*@
  loop invariant i + j == n + j;
  loop invariant (b == 1 && i > j) || (b == 0 && j >= i);
  loop invariant i - j == (n % 2 == 1 ? 1 : 0);
  loop invariant n <= 2*k;
  loop invariant \forall integer m; 0 <= m < n ==> m % 2 == 0 ==> b == 0;
  loop invariant \forall integer m; 0 <= m < n ==> m % 2 == 1 ==> b == 1;
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
