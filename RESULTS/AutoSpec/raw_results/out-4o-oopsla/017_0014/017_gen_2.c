

void foo017(int n) {
 int k=1;
 int i=1;
 int j=0;
 
 /*@
 loop invariant j <= i;
 loop invariant j < i;
 loop invariant 1 <= k;
 loop invariant 1 <= i;
 loop invariant 0 <= j;
 loop invariant 0 <= i;
 loop assigns k;
 loop assigns j;
 loop assigns i;
 */
 while(i < n) {
  j = 0;
  /*@
  loop invariant j <= i;
  loop invariant j < i;
  loop invariant i <= n;
  loop invariant k >= (i*(i-1))/2;
  loop invariant k == \sum(0, i-1, i-j);
  loop invariant 0 <= j <= i;
  loop invariant \forall integer m; 0 <= m < j ==> 0 <= i-m <= i;
  loop invariant j <= i;
  loop invariant i <= n;
  loop invariant 1 <= k;
  loop invariant 0 <= j;
  loop invariant 0 <= i;
  loop assigns k;
  loop assigns j;
  */
  while(j < i) {
      k += (i-j);
      j++;
  }
  i++;
 }
 // @ assert k >= n ;
 
}
