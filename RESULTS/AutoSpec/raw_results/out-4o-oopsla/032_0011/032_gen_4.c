

void foo032(int b,int j) {
  int k = 100;
  int i = j;
  int n = 0;
  /*@
  loop invariant i + j == n + 2 * j_initial;
  loop invariant b == (n % 2 == 1);
  loop invariant 0 <= i;
  loop invariant 0 <= j;
  loop invariant \forall integer p; 0 <= p < n ==> (b_initial ? p % 2 == 1 : p % 2 == 0);
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
