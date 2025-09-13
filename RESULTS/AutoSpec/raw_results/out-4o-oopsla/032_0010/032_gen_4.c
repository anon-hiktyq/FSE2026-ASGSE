

void foo032(int b,int j) {
  int k = 100;
  int i = j;
  int n = 0;
  /*@
  loop invariant 0 <= n <= 2 * k;
  loop invariant i + j == 2 * k + 2 * j_0; // Where j_0 is the initial value of j
  loop invariant (n % 2 == 0 && b == (b_0 != 0)) || (n % 2 == 1 && b == (b_0 == 0)); // Alternating `b` values, where b_0 is the initial value of b
  loop invariant \forall integer x; 0 <= x < n ==> (b == b_0 ==> i - j == 0);
  loop assigns n, b, i, j;
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
