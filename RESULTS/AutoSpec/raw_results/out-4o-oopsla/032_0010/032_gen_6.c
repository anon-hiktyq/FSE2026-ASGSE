

void foo032(int b,int j) {
  int k = 100;
  int i = j;
  int n = 0;
  /*@
  loop invariant 0 <= n <= 2 * k;
  loop invariant i + j == 2 * k + 2 * j_initial; /* where j_initial is the initial value of j */
  loop invariant (n % 2 == 0) ==> (b == b_initial); /* where b_initial is the initial value of b */
  loop invariant (n % 2 == 1) ==> (b != b_initial);
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
