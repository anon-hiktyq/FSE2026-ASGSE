

void foo017(int n) {
 int k=1;
 int i=1;
 int j=0;
 
 /*@
 loop invariant 1 <= i <= n;
 loop invariant 1 <= k;
 loop invariant j == 0;
 loop invariant \forall integer p, q; 1 <= p < i && 0 <= q < p ==> k >= p - q;
 loop assigns i;
 loop assigns k;
 loop assigns j;
 */
 while(i < n) {
  j = 0;
  /*@
  loop invariant j <= i;
  loop invariant i <= n;
  loop invariant i <= k;
  loop invariant 1 <= k;
  loop invariant 1 <= i;
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
