

void foo032(int b,int j) {
  int k = 100;
  int i = j;
  int n = 0;
  /*@
  loop invariant i + j == n + j + b;
  loop invariant i - j == n * (2*b - 1);
  loop invariant 0 <= i + j <= 2*k;
  loop invariant (b && i == j + 1) || (!b && i == j);
  loop invariant n <= 2*k;
  loop invariant 0 <= n;
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
