

void foo032(int b,int j) {
  int k = 100;
  int i = j;
  int n = 0;
  /*@
  loop invariant n <= 2 * k;
  loop invariant i - j == (n / 2) - (n - n / 2);
  loop invariant i + j == 2 * k + j + b - n;
  loop invariant i + j == 2 * k + 2 * n + 2 * j - b;
  loop invariant i + j == 2 * k + 2 * j_initial; /* where j_initial is the initial value of j */;
  loop invariant i + j == 2 * k + 2 * j_0; // where j_0 is the initial value of j;
  loop invariant i + j == 2 * k + 2 * j_0; // Where j_0 is the initial value of j;
  loop invariant i + j == 2 * k + 2 * j;
  loop invariant i + j == 2 * j_0 + n;
  loop invariant b == n % 2;
  loop invariant b == (n % 2 == 0);
  loop invariant \forall integer x; 0 <= x < n ==> (b == b_0 ==> i - j == 0);
  loop invariant 0 <= n;
  loop invariant (n % 2 == 1) ==> b != \at(b, LoopEntry);
  loop invariant (n % 2 == 1) ==> (b != b_initial);
  loop invariant (n % 2 == 1) ==> (b != \at(b, Pre));
  loop invariant (n % 2 == 0) ==> b == \at(b, LoopEntry);
  loop invariant (n % 2 == 0) ==> (b == b_initial); /* where b_initial is the initial value of b */;
  loop invariant (n % 2 == 0) ==> (b == \at(b, Pre));
  loop invariant (n % 2 == 0 ==> i == j + (n / 2)) && (n % 2 == 1 ==> i == j + (n / 2) + 1);
  loop invariant (n % 2 == 0 && b) || (n % 2 == 1 && !b);
  loop invariant (n % 2 == 0 && b == (b_0 != 0)) || (n % 2 == 1 && b == (b_0 == 0)); // Alternating `b` values, where b_0 is the initial value of b;
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
