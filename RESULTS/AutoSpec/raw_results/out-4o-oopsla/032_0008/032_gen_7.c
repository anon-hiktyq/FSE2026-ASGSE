

void foo032(int b,int j) {
  int k = 100;
  int i = j;
  int n = 0;
  /*@
  loop invariant i + j == \at(i, Pre) + \at(j, Pre) + n;
  loop invariant b == (n % 2 == 0 ? \at(b, Pre) : !\at(b, Pre));
  loop invariant \forall integer x; 0 <= x <= n ==> (x % 2 == 0 ==> b == \at(b, Pre));
  loop invariant \forall integer x; 0 <= x <= n ==> (x % 2 == 1 ==> b != \at(b, Pre));
  loop invariant \forall integer x; 0 <= x < n ==> (x % 2 == 0 ==> i == \at(i, Pre) + x/2);
  loop invariant \forall integer x; 0 <= x < n ==> (x % 2 == 1 ==> j == \at(j, Pre) + x/2 + 1);
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
