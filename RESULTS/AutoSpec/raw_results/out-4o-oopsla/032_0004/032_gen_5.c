

void foo032(int b,int j) {
  int k = 100;
  int i = j;
  int n = 0;
  /*@
  loop invariant 0 <= n <= 2 * k;
  loop invariant j - i == ((n % 2 == 0) ? 0 : 1);
  loop invariant b == (n % 2 == 1);
  loop invariant i + j == j + i;
  loop invariant (b == 0 && n % 2 == 0) || (b == 1 && n % 2 == 1);
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
