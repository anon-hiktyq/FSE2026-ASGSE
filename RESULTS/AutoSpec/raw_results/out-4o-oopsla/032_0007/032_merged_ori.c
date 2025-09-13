

void foo032(int b,int j) {
  int k = 100;
  int i = j;
  int n = 0;
  /*@
  loop invariant n <= 2*k;
  loop invariant n <= 2 * k;
  loop invariant n % 2 == 0 ==> i == j;
  loop invariant i - j == (n % 2 == 0 ? 0 : (b ? 1 : -1));
  loop invariant i - j == (b ? 1 : -1) * n / 2;
  loop invariant i + j == 2*j_0 + n; // where j_0 is the initial value of j;
  loop invariant i + j == 2*j_0 + n;
  loop invariant i + j == 2 * n + j + 1;
  loop invariant i + j == 2 * j_0 + n;
  loop invariant i + j == 2 * (n / 2) + j + (b ? 1 : 0);
  loop invariant i + j == 2 * (n / 2) + (b ? 1 : 0);
  loop invariant b == (n % 2 == 0 ? \at(b, Pre) : !\at(b, Pre));
  loop invariant b == ((n % 2) == 0 ? b_0 : !b_0);
  loop invariant 0 <= n;
  loop invariant (n % 2 == 1) ==> b != b_0;
  loop invariant (n % 2 == 0) ==> b == b_0;
  loop invariant (n % 2 == 0 && b == b_0) || (n % 2 == 1 && b != b_0);
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
