

void foo032(int b,int j) {
  int k = 100;
  int i = j;
  int n = 0;
  /*@
  loop invariant n % 2 == (b == \at(b, Pre) ? 0 : 1);
  loop invariant i + j == \at(i, Pre) + \at(j, Pre) + n;
  loop invariant n <= 2 * k;
  loop invariant n >= 0;
  loop invariant (b == \at(b, Pre)) ==> (n % 2 == 0);
  loop invariant (b != \at(b, Pre)) ==> (n % 2 == 1);
  loop invariant \at(j, Pre) <= j <= \at(j, Pre) + n;
  loop invariant j - i == n - (\at(i, Pre) - \at(j, Pre));
  loop invariant n <= 2*k;
  loop invariant n <= 2 * k;
  loop invariant j <= \at(j, Pre) + n;
  loop invariant j - \at(j, Pre) <= n;
  loop invariant b == (n % 2 == 0 ? \at(b, Pre) : !\at(b, Pre));
  loop invariant \at(j, Pre) <= j;
  loop invariant 0 <= n;
  loop invariant 0 <= j - \at(j, Pre);
  loop invariant (n % 2 == 1) ==> b != \at(b, Pre);
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
