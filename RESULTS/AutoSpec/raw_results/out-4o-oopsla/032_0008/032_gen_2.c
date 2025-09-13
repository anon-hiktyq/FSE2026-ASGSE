

void foo032(int b,int j) {
  int k = 100;
  int i = j;
  int n = 0;
  /*@
  loop invariant i + j == \at(i, Pre) + \at(j, Pre) + n; 
  loop invariant n % 2 == (b ? 0 : 1);
  loop invariant i - j == \at(i, Pre) - \at(j, Pre);
  loop invariant \forall integer m; 0 <= m <= n ==> (m % 2 == 0 ? b == \at(b, Pre) : b != \at(b, Pre));
  loop invariant n <= 2*k;
  loop invariant n <= 2 * k;
  loop invariant b == (n % 2 == 0 ? \at(b, Pre) : !\at(b, Pre));
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
