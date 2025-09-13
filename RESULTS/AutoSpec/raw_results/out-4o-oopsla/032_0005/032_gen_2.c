

void foo032(int b,int j) {
  int k = 100;
  int i = j;
  int n = 0;
  /*@
  loop invariant 0 <= n <= 2 * k;
  loop invariant i + j == 2 * j + n;
  loop invariant (b == 1) ==> (i == j + n / 2);
  loop invariant (b == 0) ==> (i == j + (n + 1) / 2);
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
