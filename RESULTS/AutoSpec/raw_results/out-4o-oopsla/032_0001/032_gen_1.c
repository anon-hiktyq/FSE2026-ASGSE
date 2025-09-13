

void foo032(int b,int j) {
  int k = 100;
  int i = j;
  int n = 0;
  /*@
  loop invariant 0 <= n <= 2 * k;
  loop invariant i + j == 2 * j_0 + n; // where j_0 is the initial value of `j`
  loop invariant (b && i == j_0 + n / 2 + 1) || (!b && i == j_0 + n / 2);
  loop invariant (!b && j == j_0 + n / 2) || (b && j == j_0 + n / 2 - 1);
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
