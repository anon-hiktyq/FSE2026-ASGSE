

void foo032(int b,int j) {
  int k = 100;
  int i = j;
  int n = 0;
  /*@
  loop invariant n <= 2 * k;
  loop invariant j - \at(j, Pre) == n / 2;
  loop invariant i - j == (n % 2 == 0 ? 0 : (b_0 ? 1 : -1));
  loop invariant i - \at(i, Pre) == n / 2;
  loop invariant i + j == 2 * k + 2 * j_initial;
  loop invariant i + j == 2 * k + 2 * j_0; // where j_0 is the initial value of j;
  loop invariant i + j == 2 * k + 2 * j_0; // Preserving the sum of i and j, where j_0 is the initial value of j.;
  loop invariant i + j == 2 * k + 2 * j_0;
  loop invariant i + j == 2 * k + 2 * j;
  loop invariant i + j == 2 * k + 2 * b + 2 * j_0 - 1;
  loop invariant i + j == 2 * k + 2 * b + 2 * j0;;
  loop invariant i + j == 2 * j_0 + n;
  loop invariant 0 <= n;
  loop invariant (n % 2 == 1) ==> (b != \at(b, Pre));
  loop invariant (n % 2 == 0) ==> (b == \at(b, Pre));
  loop invariant (n % 2 == 0 && b) || (n % 2 == 1 && !b);
  loop invariant (n % 2 == 0 && b == b_0) || (n % 2 == 1 && b != b_0);
  loop invariant (n % 2 == 0 && b == \at(b, Pre)) || (n % 2 == 1 && b != \at(b, Pre));
  loop invariant (b == 1) ==> i - j == 1;
  loop invariant (b == 0) ==> i == j;
  loop invariant (b == 0 ==> i - j == -1) && (b == 1 ==> i - j == 1);
  loop invariant (b && i == j + n / 2 + 1) || (!b && i == j + n / 2);
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
