

void foo032(int b,int j) {
  int k = 100;
  int i = j;
  int n = 0;
  /*@
  loop invariant n <= 2*k;
  loop invariant n <= 2 * k;
  loop invariant n % 2 == b;
  loop invariant i - j == (n % 2 == 0 ? 0 : 1);
  loop invariant i - j == (b ? n : -n);
  loop invariant i + j == 2*k + \old(i) + \old(j);
  loop invariant i + j == 2*j_0 + n;
  loop invariant i + j == 2 * j_initial + n;
  loop invariant i + j == 2 * j_0 + n;
  loop invariant i + j == 2 * j + n;
  loop invariant i + j == 2 * (n / 2) + j;
  loop invariant b == (n % 2 == 0);
  loop invariant b == (\old(b) ^ (n % 2));
  loop invariant b == !(n % 2 == 0);
  loop invariant 0 <= n;
  loop invariant (b == 1) ==> (i == j + n / 2);
  loop invariant (b == 0) ==> (i == j + (n + 1) / 2);
  loop invariant (b && i == j + 1) || (!b && i == j);
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
