

void foo032(int b,int j) {
  int k = 100;
  int i = j;
  int n = 0;
  /*@
  loop invariant 0 <= n <= 2 * k;
  loop invariant i - j == (n % 2 == 0 ? 0 : (b ? 1 : -1));
  loop invariant b == (n % 2 == 0 ? \at(b, Pre) : !\at(b, Pre));
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
