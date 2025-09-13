

void foo032(int b,int j) {
  int k = 100;
  int i = j;
  int n = 0;
  /*@
  loop invariant i + j == n + j;
  loop invariant i - j == (n % 2 ? 1 : 0);
  loop invariant 0 <= n <= 2 * k;
  loop invariant b == (n % 2 == 0);
  loop invariant \forall integer p; 0 <= p < n ==> (p % 2 == 0 ==> i > j) && (p % 2 == 1 ==> j > i);
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
