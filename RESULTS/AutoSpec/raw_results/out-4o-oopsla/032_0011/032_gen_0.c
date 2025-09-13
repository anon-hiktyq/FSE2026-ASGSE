

void foo032(int b,int j) {
  int k = 100;
  int i = j;
  int n = 0;
  /*@
  loop invariant i + j == 2 * n + j;  
  loop invariant b == 0 || b == 1;
  loop invariant (b == 0 ==> i == j + n) && (b == 1 ==> j == i + n);
  loop invariant n >= 0;
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
